//! `filter_ast` provides an AST representation of a boolean filter expression.

use std::{
    fmt, iter,
    ops::{BitAnd, BitOr, Not},
    slice,
};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

pub mod visit;

/// A leaf node in a filter expression. This compares an individual field's value to a
/// specific operand using some operation.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Clause<F, P, O> {
    // Do not reorder these fields; their order is important to the `Ord` trait
    field: F,
    operator: P,
    operand: O,
}

impl<F, P, O> Clause<F, P, O> {
    pub fn new(field: F, operator: P, operand: O) -> Self {
        Clause {
            field,
            operator,
            operand,
        }
    }

    /// Get the field against which this clause performs its comparison.
    pub fn field(&self) -> &F {
        &self.field
    }

    /// Get the operator used in this clause's comparison.
    pub fn operator(&self) -> &P {
        &self.operator
    }

    /// Get the operand for this clause's comparison.
    pub fn operand(&self) -> &O {
        &self.operand
    }

    pub fn as_tuple(&self) -> (&F, &P, &O) {
        (self.field(), self.operator(), self.operand())
    }

    pub fn into_tuple(self) -> (F, P, O) {
        (self.field, self.operator, self.operand)
    }
}

impl<F: fmt::Display, P: fmt::Display, O: fmt::Display> fmt::Display for Clause<F, P, O> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {} {}", self.field, self.operator, self.operand)
    }
}

impl<F, P, O, Rhs> BitAnd<Rhs> for Clause<F, P, O>
where
    Expr<F, P, O>: BitAnd<Rhs, Output = Expr<F, P, O>>,
{
    type Output = Expr<F, P, O>;

    fn bitand(self, rhs: Rhs) -> Self::Output {
        Expr::from(self) & rhs
    }
}

impl<F, P, O, Rhs> BitOr<Rhs> for Clause<F, P, O>
where
    Expr<F, P, O>: BitOr<Rhs, Output = Expr<F, P, O>>,
{
    type Output = Expr<F, P, O>;

    fn bitor(self, rhs: Rhs) -> Self::Output {
        Expr::from(self) | rhs
    }
}

/// Invert the filter expression by wrapping the clause in a tree with `Not` as its operator.
impl<F, P, O> Not for Clause<F, P, O> {
    type Output = Expr<F, P, O>;

    fn not(self) -> Self::Output {
        !Expr::from(self)
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "lowercase"))]
pub enum Logic {
    /// All rules must match for the tree to match
    And,
    /// Any rule must match for the tree to match
    Or,
    /// No rule may match for the tree to match
    Not,
}

/// A compound node in a filter expression, consisting of a logical operator and a set of
/// child expressions.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Tree<T> {
    operator: Logic,
    rules: Vec<T>,
}

impl<T> Tree<T> {
    pub fn new(operator: Logic, rules: Vec<T>) -> Self {
        Self { operator, rules }
    }

    pub fn operator(&self) -> Logic {
        self.operator
    }

    pub fn rules(&self) -> &[T] {
        &self.rules
    }

    /// Create an instance by collecting the rules from an iterator.
    ///
    /// # Example
    /// ```rust
    /// # use filter_ast::{Clause, Tree, Logic};
    /// let rules = vec![
    ///     Clause::new("name", "=", "jim"),
    ///     Clause::new("age", ">", "10")
    /// ];
    ///
    /// let tree = Tree::from_iter(
    ///     Logic::And,
    ///     rules.into_iter().filter(|f| *f.field() != "age")
    /// );
    ///
    /// assert_eq!(1, tree.rules().len());
    /// ```
    pub fn from_iter(operator: Logic, rules: impl Iterator<Item = T>) -> Self {
        Tree::new(operator, rules.collect())
    }

    /// Create a new tree by applying a transform to all its rules.
    ///
    /// # Example
    /// ```rust
    /// # use filter_ast::{Tree, Logic};
    /// let tree = Tree::new(Logic::Or, vec![1, 2]);
    /// let tree2 = tree.map(|x| x * 10);
    /// assert_eq!(Tree::new(Logic::Or, vec![10, 20]), tree2);
    /// ```
    pub fn map<U, F>(self, transform: F) -> Tree<U>
    where
        F: FnMut(T) -> U,
    {
        Tree::from_iter(self.operator(), self.rules.into_iter().map(transform))
    }
}

impl<T: Ord> Tree<T> {
    /// Sort the rules in the tree.
    pub fn sort(&mut self) {
        self.rules.sort()
    }
}

/// A filter expression.
///
/// Filter expressions are an abstract representation of a function `(val: T) -> bool`.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Expr<F, P, O> {
    /// A sub-tree in the filter expression.
    Tree(Tree<Expr<F, P, O>>),
    /// A leaf node in the filter expression.
    Clause(Clause<F, P, O>),
}

impl<F, P, O> Expr<F, P, O> {
    /// Create a new clause wrapped in an `Expr`.
    pub fn new_clause(field: F, operator: P, operand: O) -> Self {
        Clause::new(field, operator, operand).into()
    }

    pub fn is_tree(&self) -> bool {
        match self {
            Expr::Tree(_) => true,
            Expr::Clause(_) => false,
        }
    }

    pub fn is_clause(&self) -> bool {
        !self.is_tree()
    }

    pub fn as_tree(&self) -> Option<&Tree<Expr<F, P, O>>> {
        if let Expr::Tree(tree) = &self {
            Some(tree)
        } else {
            None
        }
    }

    pub fn as_clause(&self) -> Option<&Clause<F, P, O>> {
        if let Expr::Clause(clause) = &self {
            Some(clause)
        } else {
            None
        }
    }

    /// Apply a mapping function to each clause in the expression, creating a new expression.
    ///
    /// The mapping function is allowed to return a new tree; this enables expansion of one
    /// clause into a nested sub-tree.
    pub fn map<F2, P2, O2, TF>(self, mut transform: TF) -> Expr<F2, P2, O2>
    where
        TF: FnMut(Clause<F, P, O>) -> Expr<F2, P2, O2>,
    {
        self.map_recursive(&mut transform)
    }

    /// Implementation helper for `map`, allowing callers to pass an owned closure while using a `&mut`
    /// reference internally to call the function multiple times.
    fn map_recursive<F2, P2, O2, TF>(self, transform: &mut TF) -> Expr<F2, P2, O2>
    where
        TF: FnMut(Clause<F, P, O>) -> Expr<F2, P2, O2>,
    {
        match self {
            Expr::Clause(clause) => transform(clause),
            Expr::Tree(tree) => tree.map(|sub| sub.map_recursive(transform)).into(),
        }
    }

    /// Visit all clauses in depth-first order.
    ///
    /// For more advanced visiting, see [`visit::Visit`].
    pub fn clauses<'a>(&'a self) -> Clauses<'a, F, P, O> {
        Clauses {
            expr: self,
            stack: Vec::new(),
            has_visited_root: false,
        }
    }
}

impl<F, P, O> From<Clause<F, P, O>> for Expr<F, P, O> {
    fn from(v: Clause<F, P, O>) -> Self {
        Self::Clause(v)
    }
}

impl<F, P, O> From<Tree<Expr<F, P, O>>> for Expr<F, P, O> {
    fn from(v: Tree<Expr<F, P, O>>) -> Self {
        Self::Tree(v)
    }
}

/// Create a new expression representing the intersection of the provided expressions.
///
/// # Usage
/// ```rust
/// # use filter_ast::{Expr, Logic};
/// let a = Expr::new_clause("field", "=", "v1");
/// let b = Expr::new_clause("other", "=", "a");
/// let c = a & b;
/// let c_tree = c.as_tree().unwrap();
/// assert_eq!(c_tree.operator(), Logic::And);
/// assert_eq!(c_tree.rules()[0].as_clause().unwrap().field(), &"field");
/// assert_eq!(c_tree.rules()[1].as_clause().unwrap().field(), &"other");
/// ```
///
/// # Tree Simplification
/// This operation will try to avoid increasing tree depth by merging rules from input tree expressions
/// whose operator is `Logic::And`. For example, `(a & b) & (c & d & e)` will produce `a & b & c & d & e`.
impl<F, P, O> BitAnd for Expr<F, P, O> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        let mut rules = match self {
            Self::Tree(Tree {
                operator: Logic::And,
                rules,
            }) => rules,
            _ => vec![self],
        };

        match rhs {
            Self::Tree(Tree {
                operator: Logic::And,
                rules: rhs_rules,
            }) => rules.extend(rhs_rules),
            _ => rules.extend(iter::once(rhs)),
        };

        Tree {
            operator: Logic::And,
            rules,
        }
        .into()
    }
}

impl<F, P, O> BitAnd<Clause<F, P, O>> for Expr<F, P, O> {
    type Output = Self;

    fn bitand(self, rhs: Clause<F, P, O>) -> Self::Output {
        self & Expr::from(rhs)
    }
}

impl<F, P, O> BitAnd<Tree<Expr<F, P, O>>> for Expr<F, P, O> {
    type Output = Self;

    fn bitand(self, rhs: Tree<Expr<F, P, O>>) -> Self::Output {
        self & Expr::from(rhs)
    }
}

/// Create a new expression representing the union of the provided expressions.
///
/// # Usage
/// ```rust
/// # use filter_ast::{Expr, Logic};
/// let a = Expr::new_clause("field", "=", "v1");
/// let b = Expr::new_clause("other", "=", "a");
/// let c = a | b;
/// let c_tree = c.as_tree().unwrap();
/// assert_eq!(c_tree.operator(), Logic::Or);
/// assert_eq!(c_tree.rules()[0].as_clause().unwrap().field(), &"field");
/// assert_eq!(c_tree.rules()[1].as_clause().unwrap().field(), &"other");
/// ```
///
/// # Tree Simplification
/// This operation will try to avoid increasing tree depth by merging rules from input tree expressions
/// whose operator is `Logic::And`. For example, `(a | b) | (c | d | e)` will produce `a | b | c | d | e`.
impl<F, P, O> BitOr for Expr<F, P, O> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        let mut rules = match self {
            Self::Tree(Tree {
                operator: Logic::Or,
                rules,
            }) => rules,
            _ => vec![self],
        };

        match rhs {
            Self::Tree(Tree {
                operator: Logic::Or,
                rules: rhs_rules,
            }) => rules.extend(rhs_rules),
            _ => rules.extend(iter::once(rhs)),
        };

        Tree {
            operator: Logic::Or,
            rules,
        }
        .into()
    }
}

impl<F, P, O> BitOr<Clause<F, P, O>> for Expr<F, P, O> {
    type Output = Self;

    fn bitor(self, rhs: Clause<F, P, O>) -> Self::Output {
        self | Expr::from(rhs)
    }
}

impl<F, P, O> BitOr<Tree<Expr<F, P, O>>> for Expr<F, P, O> {
    type Output = Self;

    fn bitor(self, rhs: Tree<Expr<F, P, O>>) -> Self::Output {
        self | Expr::from(rhs)
    }
}

/// Create a new expression representing the inverse of the provided expression.
impl<F, P, O> Not for Expr<F, P, O> {
    type Output = Self;

    fn not(self) -> Self::Output {
        Tree::new(Logic::Not, vec![self]).into()
    }
}

/// Iterator over all clauses in an expression.
///
/// Created with [`Expr::clauses`].
#[derive(Clone)]
pub struct Clauses<'ast, F, P, O> {
    expr: &'ast Expr<F, P, O>,
    stack: Vec<slice::Iter<'ast, Expr<F, P, O>>>,
    has_visited_root: bool,
}

impl<'ast, F, P, O> Clauses<'ast, F, P, O> {
    fn start_tree(&mut self, tree: &'ast Tree<Expr<F, P, O>>) {
        self.stack.push(tree.rules().iter());
    }
}

impl<'ast, F, P, O> Iterator for Clauses<'ast, F, P, O> {
    type Item = &'ast Clause<F, P, O>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.stack.last_mut() {
            Some(i) => match i.next() {
                Some(Expr::Clause(clause)) => Some(clause),
                Some(Expr::Tree(tree)) => {
                    self.start_tree(tree);
                    self.next()
                }
                None => {
                    self.stack.pop();
                    self.next()
                }
            },
            None if !self.has_visited_root => {
                self.has_visited_root = true;
                match self.expr {
                    Expr::Clause(clause) => Some(clause),
                    Expr::Tree(tree) => {
                        self.start_tree(tree);
                        self.next()
                    }
                }
            }
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[allow(clippy::clone_double_ref)]
    fn expand_ipaddr(
        clause: Clause<&'static str, &'static str, &'static str>,
    ) -> Expr<&'static str, &'static str, &'static str> {
        if *clause.field() == ".ipaddr" {
            Tree::new(
                Logic::Or,
                vec![
                    Expr::new_clause(
                        "clientAddr",
                        clause.operator().clone(),
                        clause.operand().clone(),
                    ),
                    Expr::new_clause(
                        "serverAddr",
                        clause.operator().clone(),
                        clause.operand().clone(),
                    ),
                    Expr::new_clause(
                        "senderAddr",
                        clause.operator().clone(),
                        clause.operand().clone(),
                    ),
                    Expr::new_clause(
                        "receiverAddr",
                        clause.operator().clone(),
                        clause.operand().clone(),
                    ),
                ],
            )
            .into()
        } else {
            clause.into()
        }
    }

    /// Test that `Expr::map` can be used to expand clauses into subtrees
    #[test]
    fn expand_filter() {
        let filter = Expr::from(Tree::new(
            Logic::And,
            vec![
                Expr::new_clause("serverAddr", "=", "1"),
                Expr::new_clause(".ipaddr", "=", "2"),
                Expr::new_clause("serverAddr", "=", "3"),
            ],
        ));

        let mapped = filter.map(&expand_ipaddr);

        let m_tree = mapped
            .as_tree()
            .expect("Filter mapping should not convert tree to clause");
        assert_eq!(3, m_tree.rules().len());
        assert!(m_tree.rules[1].is_tree());
    }

    /// Test that `Expr::map` compiles and runs with a closure
    #[test]
    fn map_filter_with_closure() {
        let filter = Expr::from(Tree::new(
            Logic::Or,
            vec![
                Expr::new_clause("server", "=", "a"),
                Expr::new_clause(".device", "=", "a"),
            ],
        ));

        let mapped = filter.map(|clause| {
            if *clause.field() == ".device" {
                Expr::new_clause("example", "!=", "b")
            } else {
                clause.into()
            }
        });

        let m_tree = mapped
            .as_tree()
            .expect("Filter mapping should not convert tree to clause");

        assert_eq!(*m_tree.rules()[1].as_clause().unwrap().field(), "example");
    }

    #[test]
    fn clause_iter() {
        let filter = Expr::from(Tree::new(
            Logic::Or,
            vec![
                Expr::new_clause(0, "=", "a"),
                Tree::new(
                    Logic::And,
                    vec![Expr::new_clause(1, "=", "a"), Expr::new_clause(2, "=", "a")],
                )
                .into(),
                Expr::new_clause(3, "=", "a"),
            ],
        ));

        let indices = filter
            .clauses()
            .map(|clause| *clause.field())
            .collect::<Vec<_>>();
        let expected = (0..=3).collect::<Vec<_>>();
        assert_eq!(indices, expected);
    }

    #[test]
    fn bitand_clauses() {
        let expr = Clause::new("server", "=", "a")
            & Clause::new("client", "=", "b")
            & Clause::new("url", "~", "login");
        let tree: Tree<Expr<_, _, _>> = expr.as_tree().cloned().unwrap();
        assert_eq!(tree.operator, Logic::And);
        assert_eq!(tree.rules.len(), 3);
    }
}
