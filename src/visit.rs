//! Traversal of a shared borrow of a filter expression.

use crate::{Clause, Expr, Tree};

/// Visitor for a filter expression.
pub trait Visit<'ast, F, P, O> {
    /// Visit a leaf node in the filter expression.
    fn visit_clause(&mut self, clause: &'ast Clause<F, P, O>) {
        // Use `clause` so that the documentation doesn't show an underscore-prefixed name
        // and the compiler is happy.
        std::mem::drop(clause);
    }

    /// Visit a compound filter. The default implementation will visit each sub-expression
    /// in declaration order.
    fn visit_tree(&mut self, tree: &'ast Tree<Expr<F, P, O>>) {
        for expr in tree.rules() {
            self.visit_expr(expr);
        }
    }

    /// Visit a filter expression. By default this will dispatch to the `visit` method which
    /// matches the expression variant.
    fn visit_expr(&mut self, expr: &'ast Expr<F, P, O>) {
        match expr {
            Expr::Clause(clause) => self.visit_clause(clause),
            Expr::Tree(tree) => self.visit_tree(tree),
        }
    }
}
