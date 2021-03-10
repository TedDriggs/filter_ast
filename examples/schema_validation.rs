use std::net::{AddrParseError, IpAddr};

use filter_ast::{visit::Visit, Clause, Expr, Tree};

#[derive(Debug, Clone, Copy)]
enum Field {
    Name,
    Tag,
    IpAddr,
}

#[derive(Debug, Clone, Copy)]
enum Operator {
    Eq,
    FuzzyEq,
    NotEq,
}

#[derive(Debug)]
enum Operand {
    Text(String),
    IpAddr(IpAddr),
}

impl Operand {
    /// Parse an operand string into an operand using the specified interpretation.
    fn parse_as(ty: OperandType, value: String) -> Result<Self, AddrParseError> {
        match ty {
            OperandType::Text => Ok(Operand::Text(value)),
            OperandType::IpAddr => value.parse().map(Operand::IpAddr),
        }
    }
}

/// Reference to operand types that can appear in a schema. This is preferred over
/// [`std::mem::Discriminant`] because that is opaque and cumbersome to use for this purpose.
///
/// Production code may choose to replace this with a proc-macro derivation.
enum OperandType {
    Text,
    IpAddr,
}

/// Get the operators valid for a particular field. This implementation chooses to hard-code
/// that relationship, but that isn't required.
fn get_operators_for(field: Field) -> &'static [Operator] {
    match field {
        Field::Name | Field::Tag => &[Operator::Eq, Operator::FuzzyEq, Operator::NotEq],
        Field::IpAddr => &[Operator::Eq, Operator::NotEq],
    }
}

fn get_operand_type_for(field: Field, operator: Operator) -> Option<OperandType> {
    match (field, operator) {
        (Field::IpAddr, Operator::Eq) | (Field::IpAddr, Operator::NotEq) => {
            Some(OperandType::IpAddr)
        }
        (Field::Name, _) | (Field::Tag, _) => Some(OperandType::Text),
        _ => None,
    }
}

#[derive(Debug)]
enum ClauseError {
    InvalidOperator {
        seen: Operator,
        expected: &'static [Operator],
    },
    Parse(AddrParseError),
}

fn validate_clause(
    clause: Clause<Field, Operator, String>,
) -> Result<Expr<Field, Operator, Operand>, ClauseError> {
    let (field, operator, operand) = clause.into_tuple();
    let operand = Operand::parse_as(
        get_operand_type_for(field, operator).ok_or_else(|| ClauseError::InvalidOperator {
            seen: operator,
            expected: get_operators_for(field),
        })?,
        operand,
    )
    .map_err(ClauseError::Parse)?;
    Ok(Expr::new_clause(field, operator, operand))
}

#[derive(Debug)]
struct Error {
    error: ClauseError,
    /// Path to clause, expressed as tree rule indices starting from the root
    path: Vec<usize>,
}

#[derive(Default)]
struct AllErrors {
    errors: Vec<Error>,
    current_path: Vec<usize>,
}

impl<'ast> Visit<'ast, Field, Operator, String> for AllErrors {
    fn visit_clause(&mut self, clause: &'ast Clause<Field, Operator, String>) {
        if let Err(error) = validate_clause(clause.clone()) {
            self.errors.push(Error {
                error,
                path: self.current_path.clone(),
            });
        }
    }

    fn visit_tree(&mut self, tree: &'ast Tree<Expr<Field, Operator, String>>) {
        for (idx, rule) in tree.rules().iter().enumerate() {
            self.current_path.push(idx);
            self.visit_expr(rule);
            self.current_path.pop();
        }
    }
}

fn process_expr(
    expr: Expr<Field, Operator, String>,
) -> Result<Expr<Field, Operator, Operand>, Vec<Error>> {
    // We attempt the fast-path conversion, then in case of a problem slow down and gather up errors for
    // each clause to return to the client.
    expr.clone().try_map(validate_clause).or_else(|_| {
        let mut visitor = AllErrors::default();
        visitor.visit_expr(&expr);
        Err(visitor.errors)
    })
}

fn main() {
    let a = Clause::new(Field::Name, Operator::Eq, "Example".to_string());
    let b = Clause::new(Field::IpAddr, Operator::FuzzyEq, "1.2.3.4".to_string());
    let c = Clause::new(Field::IpAddr, Operator::NotEq, "999".to_string());
    let expr = a & (b | c);
    let _ = dbg!(process_expr(expr));
}
