#![allow(clippy::result_large_err)]

use std::borrow::Borrow;
use std::fmt;

use pest::{Parser, error::Error};
use thiserror::Error as ThisError;

#[allow(clippy::large_enum_variant)]
#[derive(ThisError, Debug)]
pub enum SymbologyError {
    #[error("parse error")]
    ParseError(#[from] Error<Rule>),
    #[error("internal cst grammar error; {0:?}")]
    GrammarError(&'static str),
    #[error("suffix cannot be represented as CMS")]
    NoRepresentationAsCMS,
    #[error("suffix cannot be represented as CQS")]
    NoRepresentationAsCQS,
    #[error("suffix cannot be represented as Nasdaq Integrated")]
    NoRepresentationAsNasdaq,
}

#[derive(Parser)]
#[grammar = "us/equities/grammar.peg"]
struct SymbolParser;

macro_rules! typed_string {
    ($ident:ident) => {
        #[repr(transparent)]
        #[derive(Debug, Clone, PartialEq)]
        pub struct $ident(String);

        impl Eq for $ident {}

        impl fmt::Display for $ident {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "{}", self.0)
            }
        }

        impl<T> From<T> for $ident
        where
            T: Borrow<String>,
        {
            fn from(value: T) -> Self {
                $ident(value.borrow().clone())
            }
        }

        impl AsRef<str> for $ident {
            fn as_ref(&self) -> &str {
                self.0.as_ref()
            }
        }

        impl $ident {
            #[must_use]
            pub fn as_str(&self) -> &str {
                self.0.as_ref()
            }
        }
    };
}

typed_string!(RootSymbol);
typed_string!(CQSSuffix);
typed_string!(CMSSuffix);
typed_string!(NasdaqIntegrated);

impl CQSSuffix {
    #[must_use]
    pub fn join_root(&self, root: &RootSymbol) -> String {
        format!("{}{}", &root, &self)
    }
}

impl CMSSuffix {
    #[must_use]
    pub fn join_root(&self, root: &RootSymbol) -> String {
        format!("{} {}", &root, &self)
    }
}

impl NasdaqIntegrated {
    #[must_use]
    pub fn join_root(&self, root: &RootSymbol) -> String {
        format!("{}{}", &root, &self)
    }
}

/// All known listed US equity symbology suffixes. Note that not all suffixes
/// are representable in all symbology schemes.
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, PartialEq)]
pub enum Suffix {
    Class(String),
    ClassCalled(String),
    ClassConvertible(String),
    ClassWhenIssued(String),
    Called,
    Certificate,
    Convertible,
    ContingentValueRight,
    ConvertibleCalled,
    AmountOfMostRecentDivToGoExDistribution,
    AccumulatedDivPerShareNetExpensesThroughPrevClose,
    EmergingCompanyMarketplace,
    EstimatedCashPerCreationUnit,
    ForeignNews,
    Index,
    IntraDayNavPerShare,
    Mini,
    NavPerSharePrevClose,
    PercentPaid,
    PartialPaid,
    PartCalled,
    Preferred,
    PreferredClass(String),
    PreferredClassConvertible(String),
    PreferredClassCalled(String),
    PreferredClassWhenIssued(String),
    PreferredClassWhenDistributed(String),
    PreferredWhenIssued,
    PreferredCalled,
    PreferredConvertible,
    PreferredConvertibleCalled,
    PreferredWhenDistributed,
    SecondCategoryOfPreferred(String),
    Rights,
    RightsWhenIssued,
    SmallCorporate,
    Stamped,
    MiniSettlement,
    CurrentSharesOutstandingInThousands,
    Special,
    Settlement,
    TotalCashPerCreationUnit,
    TierTwoSecurities,
    Units,
    VariableCommonRight,
    WhenDistributed,
    WhenIssued,
    Warrants,
    WithWarrants,
    WarrantsClass(String),
    WarrantsWhenIssued,
    Test,
}

impl Eq for Suffix {}

macro_rules! make_type_safe {
    ($value:expr) => {
        Ok($value.to_owned().into())
    };
}

impl Suffix {
    /// Returns a suffix string in CQS format if the suffix has a CQS representation,
    /// and `Err(SymbologyError::NoRepresentationAsCQS)` otherwise.
    ///
    /// # Example
    ///
    /// ```
    /// # use symbologyl2::us::equities::Suffix;
    /// let suffix = Suffix::Class(String::from("A"));
    /// assert_eq!(".A", suffix.cqs_suffix().unwrap().as_str());
    /// ```
    pub fn cqs_suffix(&self) -> Result<CQSSuffix, SymbologyError> {
        match self {
            Self::Class(class) => make_type_safe!(format!(".{}", class)),
            Self::ClassCalled(class) => make_type_safe!(format!(".{}.CL", class)),
            Self::ClassConvertible(class) => make_type_safe!(format!(".{}.CV", class)),
            Self::ClassWhenIssued(class) => make_type_safe!(format!(".{}w", class)),
            Self::Called => make_type_safe!(".CL"),
            Self::Certificate => make_type_safe!(".CT"),
            Self::Convertible => make_type_safe!(".CV"),
            Self::ContingentValueRight => make_type_safe!(".CVR"),
            Self::ConvertibleCalled => make_type_safe!(".CV.CL"),
            Self::AmountOfMostRecentDivToGoExDistribution => make_type_safe!(".DP"),
            Self::AccumulatedDivPerShareNetExpensesThroughPrevClose => make_type_safe!(".DV"),
            Self::EmergingCompanyMarketplace => make_type_safe!(".EC"),
            Self::EstimatedCashPerCreationUnit => make_type_safe!(".EU"),
            Self::ForeignNews => make_type_safe!(".F.N"),
            Self::Index => make_type_safe!(".ID"),
            Self::IntraDayNavPerShare => make_type_safe!(".IV"),
            Self::Mini => make_type_safe!(".MN"),
            Self::NavPerSharePrevClose => make_type_safe!(".NV"),
            Self::PercentPaid => make_type_safe!(".PO"),
            Self::PartialPaid => make_type_safe!(".PP"),
            Self::PartCalled => make_type_safe!(".PT.CL"),
            Self::Preferred => make_type_safe!("p"),
            Self::PreferredClass(class) => make_type_safe!(format!("p{}", class)),
            Self::PreferredClassConvertible(class) => {
                make_type_safe!(format!("p{}.CV", class))
            }
            Self::PreferredClassCalled(class) => make_type_safe!(format!("p{}.CL", class)),
            Self::PreferredWhenIssued => make_type_safe!("pw"),
            Self::PreferredClassWhenIssued(class) => make_type_safe!(format!("p{}w", class)),
            Self::PreferredCalled => make_type_safe!("p.CL"),
            Self::PreferredConvertible => make_type_safe!("p.CV"),
            Self::PreferredConvertibleCalled => make_type_safe!("p.CV.CL"),
            Self::PreferredWhenDistributed => make_type_safe!("p.WD"),
            Self::PreferredClassWhenDistributed(class) => make_type_safe!(format!("p{}.WD", class)),
            Self::SecondCategoryOfPreferred(class) => make_type_safe!(format!("pC{}", class)),
            Self::Rights => make_type_safe!("r"),
            Self::RightsWhenIssued => make_type_safe!("rw"),
            Self::SmallCorporate => make_type_safe!(".SC"),
            Self::Stamped => make_type_safe!(".SD"),
            Self::MiniSettlement => make_type_safe!(".SM"),
            Self::CurrentSharesOutstandingInThousands => make_type_safe!(".SO"),
            Self::Special => make_type_safe!(".SP"),
            Self::Settlement => make_type_safe!(".SV"),
            Self::TotalCashPerCreationUnit => make_type_safe!(".TC"),
            Self::TierTwoSecurities => make_type_safe!(".TT"),
            Self::Units => make_type_safe!(".U"),
            Self::VariableCommonRight => make_type_safe!(".VR"),
            Self::WhenDistributed => make_type_safe!(".WD"),
            Self::WhenIssued => make_type_safe!("w"),
            Self::Warrants => make_type_safe!(".WS"),
            Self::WithWarrants => make_type_safe!(".W.WS"),
            Self::WarrantsClass(class) => make_type_safe!(format!(".WS.{}", class)),
            Self::WarrantsWhenIssued => make_type_safe!(".WSw"),
            Self::Test => make_type_safe!(".TEST"),
        }
    }

    /// Returns a suffix string in CMS format if the suffix has a CMS representation,
    /// and `Err(SymbologyError::NoRepresentationAsCMS)` otherwise.
    ///
    /// # Example
    ///
    /// ```
    /// # use symbologyl2::us::equities::Suffix;
    /// let suffix = Suffix::Class(String::from("A"));
    /// assert_eq!("A", suffix.cms_suffix().unwrap().as_str());
    ///
    /// assert!(Suffix::Certificate.cms_suffix().is_err());
    /// ```
    pub fn cms_suffix(&self) -> Result<CMSSuffix, SymbologyError> {
        match self {
            Self::Preferred => make_type_safe!("PR"),
            Self::PreferredClass(class) => make_type_safe!(format!("PR{}", class)),
            Self::Class(class) => make_type_safe!(class),
            Self::PreferredWhenDistributed => make_type_safe!("PRWD"),
            Self::WhenDistributed => make_type_safe!("WD"),
            Self::Warrants => make_type_safe!("WS"),
            Self::WarrantsClass(class) => make_type_safe!(format!("WS{}", class)),
            Self::Called => make_type_safe!("CL"),
            Self::ClassCalled(class) => make_type_safe!(format!("{}CL", class)),
            Self::PreferredCalled => make_type_safe!("PRCL"),
            Self::PreferredClassCalled(class) => make_type_safe!(format!("PR{}CL", class)),
            Self::PreferredClassWhenIssued(class) => make_type_safe!(format!("PR{}WI", class)),
            Self::EmergingCompanyMarketplace => make_type_safe!("EC"),
            Self::PartialPaid => make_type_safe!("PP"),
            Self::Convertible => make_type_safe!("CV"),
            Self::ConvertibleCalled => make_type_safe!("CVCL"),
            Self::ClassConvertible(class) => make_type_safe!(format!("{}CV", class)),
            Self::PreferredClassConvertible(class) => make_type_safe!(format!("PR{}CV", class)),
            Self::PreferredClassWhenDistributed(class) => make_type_safe!(format!("PR{}WD", class)),
            Self::Rights => make_type_safe!("RT"),
            Self::Units => make_type_safe!("U"),
            Self::WhenIssued => make_type_safe!("WI"),
            Self::RightsWhenIssued => make_type_safe!("RTWI"),
            Self::PreferredWhenIssued => make_type_safe!("PRWI"),
            Self::ClassWhenIssued(class) => make_type_safe!(format!("{}WI", class)),
            Self::WarrantsWhenIssued => make_type_safe!("WSWI"),
            Self::Test => make_type_safe!("TEST"),
            Self::Certificate
            | Self::ContingentValueRight
            | Self::AmountOfMostRecentDivToGoExDistribution
            | Self::AccumulatedDivPerShareNetExpensesThroughPrevClose
            | Self::EstimatedCashPerCreationUnit
            | Self::ForeignNews
            | Self::NavPerSharePrevClose
            | Self::Index
            | Self::IntraDayNavPerShare
            | Self::Mini
            | Self::PercentPaid
            | Self::PartCalled
            | Self::PreferredConvertible
            | Self::PreferredConvertibleCalled
            | Self::SecondCategoryOfPreferred(_)
            | Self::SmallCorporate
            | Self::Stamped
            | Self::MiniSettlement
            | Self::CurrentSharesOutstandingInThousands
            | Self::Special
            | Self::Settlement
            | Self::TotalCashPerCreationUnit
            | Self::TierTwoSecurities
            | Self::VariableCommonRight
            | Self::WithWarrants => Err(SymbologyError::NoRepresentationAsCMS),
        }
    }

    /// Returns a suffix string in NASDAQ integrated format if the suffix has a CMS representation,
    /// and `Err(SymbologyError::NoRepresentationAsNasdaq)` otherwise.
    ///
    /// # Example
    ///
    /// ```
    /// # use symbologyl2::us::equities::Suffix;
    /// let suffix = Suffix::PreferredClass(String::from("A"));
    /// assert_eq!("-A", suffix.nasdaq_integrated_suffix().unwrap().as_str());
    ///
    /// assert!(Suffix::Certificate.nasdaq_integrated_suffix().is_err());
    /// ```
    pub fn nasdaq_integrated_suffix(&self) -> Result<NasdaqIntegrated, SymbologyError> {
        match self {
            Self::Preferred => make_type_safe!("-"),
            Self::PreferredClass(class) => make_type_safe!(format!("-{}", class)),
            Self::Class(class) => make_type_safe!(format!(".{}", class)),
            Self::PreferredWhenDistributed => make_type_safe!("-$"),
            Self::WhenDistributed => make_type_safe!("$"),
            Self::Warrants => make_type_safe!("+"),
            Self::WarrantsClass(class) => make_type_safe!(format!("+{}", class)),
            Self::Called => make_type_safe!("*"),
            Self::ClassCalled(class) => make_type_safe!(format!(".{}*", class)),
            Self::PreferredCalled => make_type_safe!("-*"),
            Self::PreferredClassCalled(class) => make_type_safe!(format!("-{}*", class)),
            Self::PreferredClassWhenIssued(class) => make_type_safe!(format!("-{}#", class)),
            Self::EmergingCompanyMarketplace => make_type_safe!("!"),
            Self::PartialPaid => make_type_safe!("@"),
            Self::Convertible => make_type_safe!("%"),
            Self::ConvertibleCalled => make_type_safe!("%*"),
            Self::ClassConvertible(class) => make_type_safe!(format!(".{}%", class)),
            Self::PreferredClassConvertible(class) => make_type_safe!(format!("-{}%", class)),
            Self::PreferredClassWhenDistributed(class) => make_type_safe!(format!("-{}$", class)),
            Self::Rights => make_type_safe!("^"),
            Self::Units => make_type_safe!("="),
            Self::WhenIssued => make_type_safe!("#"),
            Self::RightsWhenIssued => make_type_safe!("^#"),
            Self::PreferredWhenIssued => make_type_safe!("-#"),
            Self::ClassWhenIssued(class) => make_type_safe!(format!(".{}#", class)),
            Self::WarrantsWhenIssued => make_type_safe!("+#"),
            Self::Test => make_type_safe!("~"),
            Self::Certificate
            | Self::ContingentValueRight
            | Self::AmountOfMostRecentDivToGoExDistribution
            | Self::AccumulatedDivPerShareNetExpensesThroughPrevClose
            | Self::EstimatedCashPerCreationUnit
            | Self::ForeignNews
            | Self::NavPerSharePrevClose
            | Self::Index
            | Self::IntraDayNavPerShare
            | Self::Mini
            | Self::PercentPaid
            | Self::PartCalled
            | Self::PreferredConvertible
            | Self::PreferredConvertibleCalled
            | Self::SecondCategoryOfPreferred(_)
            | Self::SmallCorporate
            | Self::Stamped
            | Self::MiniSettlement
            | Self::CurrentSharesOutstandingInThousands
            | Self::Special
            | Self::Settlement
            | Self::TotalCashPerCreationUnit
            | Self::TierTwoSecurities
            | Self::VariableCommonRight
            | Self::WithWarrants => Err(SymbologyError::NoRepresentationAsNasdaq),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Symbol {
    root: RootSymbol,
    suffix: Option<Suffix>,
}

impl Eq for Symbol {}

impl Symbol {
    #[must_use]
    pub fn root(&self) -> &RootSymbol {
        &self.root
    }

    #[must_use]
    pub fn suffix(&self) -> Option<&Suffix> {
        self.suffix.as_ref()
    }
}

/// Parse a US equity symbol symbol in any supported format (CMS, CQS, or NASDAQ
/// integrated).
///
/// # Examples
///
/// ```
/// # use symbologyl2::us::equities::{parse, Suffix};
/// let good_parse = parse("TEST.A").unwrap();
/// assert_eq!("TEST", good_parse.root().as_str());
/// assert_eq!(Some(Suffix::Class(String::from("A"))).as_ref(), good_parse.suffix());
///
/// let bad_parse = parse("123.FOO");
/// assert!(bad_parse.is_err());
/// ```
#[allow(clippy::too_many_lines)]
pub fn parse<T: AsRef<str>>(symbol: T) -> Result<Symbol, SymbologyError> {
    use pest::iterators::{Pair, Pairs};

    macro_rules! descend {
        ($token:ident, $pair:expr) => {
            if let Some(inner) = $pair.into_inner().into_iter().next() {
                Ok(Suffix::$token(inner.as_str().to_owned()))
            } else {
                Err(SymbologyError::GrammarError(stringify!(Suffix::$token)))
            }
        };
    }

    fn parse_share_class(pair: Pair<Rule>) -> Result<Suffix, SymbologyError> {
        let mut token_iter = pair.into_inner();
        let share_class = token_iter
            .next()
            .ok_or(SymbologyError::GrammarError("missing share class"))?
            .as_str()
            .to_owned();
        if let Some(share_class_suffix) = token_iter.next() {
            match share_class_suffix.as_rule() {
                Rule::class_suffix_called => Ok(Suffix::ClassCalled(share_class)),
                Rule::class_suffix_convertible => Ok(Suffix::ClassConvertible(share_class)),
                Rule::class_suffix_when_issued => Ok(Suffix::ClassWhenIssued(share_class)),
                _ => Err(SymbologyError::GrammarError(
                    "unexpected share class suffix",
                )),
            }
        } else {
            Ok(Suffix::Class(share_class))
        }
    }

    fn parse_suffix(pair: Pair<Rule>) -> Result<Suffix, SymbologyError> {
        match pair.as_rule() {
            Rule::called => Ok(Suffix::Called),
            Rule::certificate => Ok(Suffix::Certificate),
            Rule::contingent_value_right => Ok(Suffix::ContingentValueRight),
            Rule::convertible_called => Ok(Suffix::ConvertibleCalled),
            Rule::convertible => Ok(Suffix::Convertible),
            Rule::when_issued => Ok(Suffix::WhenIssued),
            Rule::ex_distribution => Ok(Suffix::AmountOfMostRecentDivToGoExDistribution),
            Rule::accumulated_dividend => {
                Ok(Suffix::AccumulatedDivPerShareNetExpensesThroughPrevClose)
            }
            Rule::emerging_company => Ok(Suffix::EmergingCompanyMarketplace),
            Rule::estimated_cash => Ok(Suffix::EstimatedCashPerCreationUnit),
            Rule::foreign_news => Ok(Suffix::ForeignNews),
            Rule::index => Ok(Suffix::Index),
            Rule::intra_day_nav => Ok(Suffix::IntraDayNavPerShare),
            Rule::mini => Ok(Suffix::Mini),
            Rule::prev_close_nav => Ok(Suffix::NavPerSharePrevClose),
            Rule::percent_paid => Ok(Suffix::PercentPaid),
            Rule::partial_paid => Ok(Suffix::PartialPaid),
            Rule::part_called => Ok(Suffix::PartCalled),
            Rule::right_when_issued => Ok(Suffix::RightsWhenIssued),
            Rule::rights => Ok(Suffix::Rights),
            Rule::small_corporate => Ok(Suffix::SmallCorporate),
            Rule::stamped => Ok(Suffix::Stamped),
            Rule::mini_settlement => Ok(Suffix::MiniSettlement),
            Rule::shares_outstanding_in_thousands => {
                Ok(Suffix::CurrentSharesOutstandingInThousands)
            }
            Rule::special => Ok(Suffix::Special),
            Rule::settlement => Ok(Suffix::Settlement),
            Rule::total_cash => Ok(Suffix::TotalCashPerCreationUnit),
            Rule::tier_two_securities => Ok(Suffix::TierTwoSecurities),
            Rule::units => Ok(Suffix::Units),
            Rule::variable_common_rights => Ok(Suffix::VariableCommonRight),
            Rule::when_distributed => Ok(Suffix::WhenDistributed),
            Rule::warrant_base => Ok(Suffix::Warrants),
            Rule::with_warrants => Ok(Suffix::WithWarrants),
            Rule::warrants_when_issued => Ok(Suffix::WarrantsWhenIssued),
            Rule::warrants_series => descend!(WarrantsClass, pair),
            Rule::preferred_when_issued => Ok(Suffix::PreferredWhenIssued),
            Rule::preferred_convertible_called => Ok(Suffix::PreferredConvertibleCalled),
            Rule::preferred_called => Ok(Suffix::PreferredCalled),
            Rule::preferred_convertible => Ok(Suffix::PreferredConvertible),
            Rule::preferred_when_distributed => Ok(Suffix::PreferredWhenDistributed),
            Rule::preferred_second_class => descend!(SecondCategoryOfPreferred, pair),
            Rule::preferred_class_convertible => descend!(PreferredClassConvertible, pair),
            Rule::preferred_class_when_distributed => descend!(PreferredClassWhenDistributed, pair),
            Rule::preferred_class_called => descend!(PreferredClassCalled, pair),
            Rule::preferred_class_when_issued => descend!(PreferredClassWhenIssued, pair),
            Rule::preferred_class => descend!(PreferredClass, pair),
            Rule::preferred_base => Ok(Suffix::Preferred),
            Rule::test => Ok(Suffix::Test),
            Rule::share_class => parse_share_class(pair),
            _ => Err(SymbologyError::GrammarError("unexpected token")),
        }
    }

    fn parse_symbol(mut pairs: Pairs<Rule>) -> Result<Symbol, SymbologyError> {
        let root: RootSymbol = pairs
            .next()
            .ok_or(SymbologyError::GrammarError("missing symbol string"))?
            .as_str()
            .to_owned()
            .into();
        if let Some(symbol_suffix) = pairs.next() {
            let suffix = parse_suffix(symbol_suffix)?;
            Ok(Symbol {
                root,
                suffix: Some(suffix),
            })
        } else {
            Ok(Symbol { root, suffix: None })
        }
    }

    fn parse_ast_root(mut pairs: Pairs<Rule>) -> Result<Symbol, SymbologyError> {
        let symbol = pairs
            .next()
            .ok_or(SymbologyError::GrammarError("missing symbol"))?;
        let eoi = pairs
            .next()
            .ok_or(SymbologyError::GrammarError("missing EOI"))?;
        match (symbol.as_rule(), eoi.as_rule()) {
            (Rule::symbol, Rule::EOI) => parse_symbol(symbol.into_inner()),
            (_, _) => Err(SymbologyError::GrammarError("bad parse root")),
        }
    }

    let res =
        SymbolParser::parse(Rule::parse, symbol.as_ref()).map_err(SymbologyError::ParseError)?;
    parse_ast_root(res)
}

macro_rules! make_format_translator {
    ($ident:ident, $suffix_getter:ident) => {
        /// Convert a symbol string in any supported format to the target format.
        pub fn $ident(symbol: &str) -> Result<String, SymbologyError> {
            let Symbol { root, suffix } = parse(symbol)?;
            if let Some(suffix) = suffix {
                let parsed_suffix = suffix.$suffix_getter()?;
                Ok(parsed_suffix.join_root(&root))
            } else {
                Ok(root.0)
            }
        }
    };
}

make_format_translator!(from_any_to_cms, cms_suffix);
make_format_translator!(from_any_to_cqs, cqs_suffix);
make_format_translator!(from_any_to_nasdaq, nasdaq_integrated_suffix);

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::too_many_lines, clippy::similar_names)]
    use super::*;

    use std::path::Path;

    use serde::Deserialize;

    const TEST_DATA_DIR: &str = "./test_data/";

    macro_rules! make_round_trip_test {
        ($test_fn:ident, $suffix_func:ident) => {
            fn $test_fn(full_symbol: &str, expected_root: &str, expected_suffix: &Suffix) {
                let Symbol { root, suffix } = parse(full_symbol).unwrap();
                let suffix = suffix.unwrap();
                assert_eq!(expected_root, root.to_string());
                assert_eq!(expected_suffix, &suffix);
                let native_suffix = suffix.$suffix_func().unwrap();
                assert_eq!(full_symbol, native_suffix.join_root(&root));
            }
        };
    }

    make_round_trip_test!(cqs_helper, cqs_suffix);
    make_round_trip_test!(cms_helper, cms_suffix);
    make_round_trip_test!(nasdaq_helper, nasdaq_integrated_suffix);

    fn full_table_test(
        full_cqs: &str,
        full_cms: &str,
        full_nasdaq: &str,
        expected_root: &str,
        expected_suffix: &Suffix,
    ) {
        cqs_helper(full_cqs, expected_root, expected_suffix);
        cms_helper(full_cms, expected_root, expected_suffix);
        nasdaq_helper(full_nasdaq, expected_root, expected_suffix);
    }

    #[test]
    pub fn test_nasdaq_trader_reference_data() {
        full_table_test("FOOp", "FOO PR", "FOO-", "FOO", &Suffix::Preferred);

        full_table_test(
            "FOOpA",
            "FOO PRA",
            "FOO-A",
            "FOO",
            &Suffix::PreferredClass(String::from("A")),
        );

        full_table_test(
            "FOO.A",
            "FOO A",
            "FOO.A",
            "FOO",
            &Suffix::Class(String::from("A")),
        );

        full_table_test(
            "FOOp.WD",
            "FOO PRWD",
            "FOO-$",
            "FOO",
            &Suffix::PreferredWhenDistributed,
        );

        full_table_test("FOO.WD", "FOO WD", "FOO$", "FOO", &Suffix::WhenDistributed);

        full_table_test("FOO.WS", "FOO WS", "FOO+", "FOO", &Suffix::Warrants);

        full_table_test(
            "FOO.WS.A",
            "FOO WSA",
            "FOO+A",
            "FOO",
            &Suffix::WarrantsClass(String::from("A")),
        );

        full_table_test("FOO.CL", "FOO CL", "FOO*", "FOO", &Suffix::Called);

        full_table_test(
            "FOO.A.CL",
            "FOO ACL",
            "FOO.A*",
            "FOO",
            &Suffix::ClassCalled(String::from("A")),
        );

        full_table_test(
            "FOOp.CL",
            "FOO PRCL",
            "FOO-*",
            "FOO",
            &Suffix::PreferredCalled,
        );

        full_table_test(
            "FOOpA.CL",
            "FOO PRACL",
            "FOO-A*",
            "FOO",
            &Suffix::PreferredClassCalled(String::from("A")),
        );

        full_table_test(
            "FOOpAw",
            "FOO PRAWI",
            "FOO-A#",
            "FOO",
            &Suffix::PreferredClassWhenIssued(String::from("A")),
        );

        full_table_test(
            "FOO.EC",
            "FOO EC",
            "FOO!",
            "FOO",
            &Suffix::EmergingCompanyMarketplace,
        );

        full_table_test("FOO.PP", "FOO PP", "FOO@", "FOO", &Suffix::PartialPaid);

        full_table_test("FOO.CV", "FOO CV", "FOO%", "FOO", &Suffix::Convertible);

        full_table_test(
            "FOO.CV.CL",
            "FOO CVCL",
            "FOO%*",
            "FOO",
            &Suffix::ConvertibleCalled,
        );

        full_table_test(
            "FOO.A.CV",
            "FOO ACV",
            "FOO.A%",
            "FOO",
            &Suffix::ClassConvertible(String::from("A")),
        );

        full_table_test(
            "FOOpA.CV",
            "FOO PRACV",
            "FOO-A%",
            "FOO",
            &Suffix::PreferredClassConvertible(String::from("A")),
        );

        full_table_test(
            "FOOpA.WD",
            "FOO PRAWD",
            "FOO-A$",
            "FOO",
            &Suffix::PreferredClassWhenDistributed(String::from("A")),
        );

        full_table_test("FOOr", "FOO RT", "FOO^", "FOO", &Suffix::Rights);

        full_table_test("FOO.U", "FOO U", "FOO=", "FOO", &Suffix::Units);

        full_table_test("FOOw", "FOO WI", "FOO#", "FOO", &Suffix::WhenIssued);

        full_table_test(
            "FOOrw",
            "FOO RTWI",
            "FOO^#",
            "FOO",
            &Suffix::RightsWhenIssued,
        );

        full_table_test(
            "FOOpw",
            "FOO PRWI",
            "FOO-#",
            "FOO",
            &Suffix::PreferredWhenIssued,
        );

        full_table_test(
            "FOO.Aw",
            "FOO AWI",
            "FOO.A#",
            "FOO",
            &Suffix::ClassWhenIssued(String::from("A")),
        );

        full_table_test(
            "FOO.WSw",
            "FOO WSWI",
            "FOO+#",
            "FOO",
            &Suffix::WarrantsWhenIssued,
        );

        full_table_test("FOO.TEST", "FOO TEST", "FOO~", "FOO", &Suffix::Test);
    }

    #[test]
    fn test_cta_symbol_table() {
        for class in ('A'..='T').chain('V'..='Z') {
            cqs_helper(
                &format!("FOO.{class}"),
                "FOO",
                &Suffix::Class(String::from(class)),
            );

            cqs_helper(
                &format!("FOO.{class}.CL"),
                "FOO",
                &Suffix::ClassCalled(String::from(class)),
            );

            cqs_helper(
                &format!("FOO.{class}.CV"),
                "FOO",
                &Suffix::ClassConvertible(String::from(class)),
            );

            cqs_helper(
                &format!("FOO.{class}w"),
                "FOO",
                &Suffix::ClassWhenIssued(String::from(class)),
            );
        }

        cqs_helper("FOO.CL", "FOO", &Suffix::Called);
        cqs_helper("FOO.CT", "FOO", &Suffix::Certificate);
        cqs_helper("FOO.CV", "FOO", &Suffix::Convertible);
        cqs_helper("FOO.CVR", "FOO", &Suffix::ContingentValueRight);
        cqs_helper("FOO.CV.CL", "FOO", &Suffix::ConvertibleCalled);

        cqs_helper(
            "FOO.DP",
            "FOO",
            &Suffix::AmountOfMostRecentDivToGoExDistribution,
        );
        cqs_helper(
            "FOO.DV",
            "FOO",
            &Suffix::AccumulatedDivPerShareNetExpensesThroughPrevClose,
        );

        cqs_helper("FOO.EC", "FOO", &Suffix::EmergingCompanyMarketplace);
        cqs_helper("FOO.EU", "FOO", &Suffix::EstimatedCashPerCreationUnit);

        cqs_helper("FOO.F.N", "FOO", &Suffix::ForeignNews);

        cqs_helper("FOO.ID", "FOO", &Suffix::Index);
        cqs_helper("FOO.IV", "FOO", &Suffix::IntraDayNavPerShare);

        cqs_helper("FOO.MN", "FOO", &Suffix::Mini);

        cqs_helper("FOO.NV", "FOO", &Suffix::NavPerSharePrevClose);

        cqs_helper("FOO.PO", "FOO", &Suffix::PercentPaid);
        cqs_helper("FOO.PP", "FOO", &Suffix::PartialPaid);
        cqs_helper("FOO.PT.CL", "FOO", &Suffix::PartCalled);
        cqs_helper("FOOp", "FOO", &Suffix::Preferred);

        for class in ('A'..='T').chain('V'..='Z') {
            cqs_helper(
                &format!("FOOp{class}"),
                "FOO",
                &Suffix::PreferredClass(String::from(class)),
            );

            cqs_helper(
                &format!("FOOp{class}.CV"),
                "FOO",
                &Suffix::PreferredClassConvertible(String::from(class)),
            );

            cqs_helper(
                &format!("FOOp{class}.CL"),
                "FOO",
                &Suffix::PreferredClassCalled(String::from(class)),
            );

            cqs_helper(
                &format!("FOOp{class}w"),
                "FOO",
                &Suffix::PreferredClassWhenIssued(String::from(class)),
            );
        }

        cqs_helper("FOOpw", "FOO", &Suffix::PreferredWhenIssued);
        cqs_helper("FOOp.CL", "FOO", &Suffix::PreferredCalled);
        cqs_helper("FOOp.CV", "FOO", &Suffix::PreferredConvertible);
        cqs_helper("FOOp.CV.CL", "FOO", &Suffix::PreferredConvertibleCalled);
        cqs_helper("FOOp.WD", "FOO", &Suffix::PreferredWhenDistributed);

        for class in ('A'..='K').chain('M'..='S') {
            cqs_helper(
                &format!("FOOpC{class}"),
                "FOO",
                &Suffix::SecondCategoryOfPreferred(String::from(class)),
            );
        }

        cqs_helper("FOOr", "FOO", &Suffix::Rights);
        cqs_helper("FOOrw", "FOO", &Suffix::RightsWhenIssued);

        cqs_helper("FOO.SC", "FOO", &Suffix::SmallCorporate);
        cqs_helper("FOO.SD", "FOO", &Suffix::Stamped);
        cqs_helper("FOO.SM", "FOO", &Suffix::MiniSettlement);
        cqs_helper(
            "FOO.SO",
            "FOO",
            &Suffix::CurrentSharesOutstandingInThousands,
        );
        cqs_helper("FOO.SP", "FOO", &Suffix::Special);
        cqs_helper("FOO.SV", "FOO", &Suffix::Settlement);

        cqs_helper("FOO.TC", "FOO", &Suffix::TotalCashPerCreationUnit);
        cqs_helper("FOO.TT", "FOO", &Suffix::TierTwoSecurities);

        cqs_helper("FOO.U", "FOO", &Suffix::Units);

        cqs_helper("FOO.VR", "FOO", &Suffix::VariableCommonRight);

        cqs_helper("FOO.WD", "FOO", &Suffix::WhenDistributed);
        cqs_helper("FOOw", "FOO", &Suffix::WhenIssued);
        cqs_helper("FOO.WS", "FOO", &Suffix::Warrants);
        cqs_helper("FOO.W.WS", "FOO", &Suffix::WithWarrants);

        for class in ('A'..='T').chain('V'..='Z') {
            cqs_helper(
                &format!("FOO.WS.{class}"),
                "FOO",
                &Suffix::WarrantsClass(String::from(class)),
            );
        }

        cqs_helper("FOO.WSw", "FOO", &Suffix::WarrantsWhenIssued);
    }

    #[derive(Debug, Deserialize)]
    struct NyseSymbolMasterEntry {
        cms_suffix: String,
        cqs_suffix: String,
    }

    #[derive(Debug, Deserialize)]
    struct NasdaqSymbolMasterEntry {
        cqs_suffix: Option<String>,
        nasdaq_suffix: String,
    }

    #[derive(Debug, Deserialize)]
    struct CatSymbolMasterEntry {
        cms_suffix: String,
    }

    macro_rules! symbol_file_reader {
        ($reader_fn:ident, $entry_ty:ty) => {
            fn $reader_fn(relative_path: &str) -> Vec<$entry_ty> {
                let path = Path::new(TEST_DATA_DIR).join(relative_path);
                let mut reader = csv::ReaderBuilder::new()
                    .delimiter(b'|')
                    .from_path(path)
                    .unwrap();
                let mut entries: Vec<$entry_ty> = Vec::new();
                for result in reader.deserialize() {
                    let record: $entry_ty = result.unwrap();
                    entries.push(record);
                }
                entries
            }
        };
    }

    #[test]
    fn test_nyse_symbol_master() {
        symbol_file_reader!(read_csv, NyseSymbolMasterEntry);

        fn run_test(test_vector: Vec<NyseSymbolMasterEntry>) {
            for entry in test_vector {
                let parsed_from_cms = parse(&entry.cms_suffix).unwrap();
                let parsed_from_cqs = parse(&entry.cqs_suffix).unwrap();
                assert_eq!(&parsed_from_cms, &parsed_from_cqs);

                if let Some(suffix) = parsed_from_cms.suffix {
                    let root_symbol = entry.cms_suffix.split(' ').next().unwrap();
                    assert_eq!(root_symbol, parsed_from_cms.root.as_str());
                    let cms_suffix = suffix.cms_suffix().unwrap();
                    assert_eq!(
                        &entry.cms_suffix,
                        &format!("{} {}", root_symbol, cms_suffix.as_str())
                    );
                    let cqs_suffix = suffix.cqs_suffix().unwrap();
                    assert_eq!(
                        &entry.cqs_suffix,
                        &format!("{}{}", root_symbol, &cqs_suffix.as_str())
                    );
                } else {
                    assert_eq!(entry.cms_suffix, parsed_from_cms.root().as_str());
                    assert_eq!(entry.cqs_suffix, parsed_from_cqs.root().as_str());
                }
            }
        }

        run_test(read_csv("nyse/american.txt"));
        run_test(read_csv("nyse/arca.txt"));
        run_test(read_csv("nyse/chicago.txt"));
        run_test(read_csv("nyse/national.txt"));
        run_test(read_csv("nyse/nyse.txt"));
    }

    #[test]
    fn test_nasdaq_symbol_master() {
        symbol_file_reader!(read_csv, NasdaqSymbolMasterEntry);

        fn run_test(test_vector: Vec<NasdaqSymbolMasterEntry>) {
            for entry in test_vector {
                let parsed_from_nasdaq = parse(&entry.nasdaq_suffix).unwrap();
                if parsed_from_nasdaq.suffix.is_none() {
                    assert_eq!(entry.nasdaq_suffix, parsed_from_nasdaq.root.as_str());
                }

                if let Some(cqs_suffix_str) = &entry.cqs_suffix {
                    let parsed_from_cqs = parse(cqs_suffix_str).unwrap();
                    assert_eq!(&parsed_from_nasdaq, &parsed_from_cqs);

                    if let Some(parsed_from_nasdaq_suffix) = &parsed_from_nasdaq.suffix {
                        let nasdaq_suffix = parsed_from_nasdaq_suffix
                            .nasdaq_integrated_suffix()
                            .unwrap();
                        let cqs_suffix = parsed_from_cqs.suffix().unwrap().cqs_suffix().unwrap();

                        assert_eq!(
                            cqs_suffix_str,
                            &format!("{}{}", parsed_from_cqs.root(), cqs_suffix.as_str())
                        );

                        assert_eq!(
                            &entry.nasdaq_suffix,
                            &format!("{}{}", parsed_from_cqs.root(), nasdaq_suffix.as_str())
                        );
                    }
                }
            }
        }

        run_test(read_csv("nasdaq/bxtraded.txt"));
        run_test(read_csv("nasdaq/nasdaqtraded.txt"));
        run_test(read_csv("nasdaq/otherlisted.txt"));
        run_test(read_csv("nasdaq/psxtraded.txt"));
    }

    #[test]
    fn test_cat_symbology_master() {
        symbol_file_reader!(read_csv, CatSymbolMasterEntry);

        for entry in read_csv("cat.txt") {
            let parsed = parse(&entry.cms_suffix).unwrap();
            if let Some(suffix) = &parsed.suffix {
                let as_cms = suffix.cms_suffix().unwrap();
                assert_eq!(
                    &entry.cms_suffix,
                    &format!("{} {}", parsed.root().as_str(), as_cms.as_str())
                );
            } else {
                assert_eq!(entry.cms_suffix, parsed.root().as_str());
            }
        }
    }

    #[test]
    fn test_no_suffix() {
        let Symbol { root, suffix } = parse("FOO").unwrap();
        assert_eq!("FOO", root.as_str());
        assert!(suffix.is_none());
    }

    #[test]
    fn test_no_representation_as_cms() {
        let symbol = parse("FOO.SP").unwrap().suffix.unwrap();
        assert!(symbol.cms_suffix().is_err());
    }

    #[test]
    fn test_no_representation_as_nasdaq() {
        let symbol = parse("FOO.SP").unwrap().suffix.unwrap();
        assert!(symbol.nasdaq_integrated_suffix().is_err());
    }

    #[test]
    fn test_bad_parse() {
        assert!(parse("FOO.ASDF").is_err());
    }

    #[test]
    fn test_display() {
        let test_root: RootSymbol = "foo".to_owned().into();
        assert_eq!("foo", format!("{}", &test_root));
    }

    #[test]
    fn test_as_str() {
        let test_root: RootSymbol = "foo".to_owned().into();
        assert_eq!("foo", test_root.as_str());
    }

    #[test]
    fn test_eq() {
        let left: RootSymbol = "foo".to_owned().into();
        let right: RootSymbol = "bar".to_owned().into();
        assert_eq!(left, left);
        assert!(left != right);
    }

    #[test]
    fn test_symbol_root() {
        let root: RootSymbol = String::from("FOO").into();
        let symbol = parse("FOO.A").unwrap();
        assert_eq!(&root, symbol.root());
    }

    #[test]
    fn test_symbol_suffix() {
        let symbol = parse("FOO.A").unwrap();
        assert_eq!(Some(&Suffix::Class(String::from("A"))), symbol.suffix());
    }

    #[test]
    fn test_from_any_to_cqs() {
        let bad_parse = from_any_to_cqs("123*#");
        assert!(bad_parse.is_err());

        let good_parse = from_any_to_cqs("FOO A").unwrap();
        assert_eq!("FOO.A", good_parse);

        let root_only = from_any_to_cqs("FOO").unwrap();
        assert_eq!("FOO", root_only);
    }

    #[test]
    fn test_from_any_to_cms() {
        let bad_parse = from_any_to_cms("123*#");
        assert!(bad_parse.is_err());

        let good_parse = from_any_to_cms("FOO.A").unwrap();
        assert_eq!("FOO A", good_parse);

        let root_only = from_any_to_cms("FOO").unwrap();
        assert_eq!("FOO", root_only);
    }

    #[test]
    fn test_from_any_to_nasdaq_integrated() {
        let bad_parse = from_any_to_nasdaq("123*#");
        assert!(bad_parse.is_err());

        let good_parse = from_any_to_nasdaq("FOOpA").unwrap();
        assert_eq!("FOO-A", good_parse);

        let root_only = from_any_to_nasdaq("FOO").unwrap();
        assert_eq!("FOO", root_only);
    }

    #[test]
    fn test_typed_string_as_ref() {
        let parsed = parse("TESTpA").unwrap();
        let root_symbol_str: &str = parsed.root().as_ref();
        let suffix = parsed.suffix().unwrap().cqs_suffix().unwrap();
        let suffix_str: &str = suffix.as_ref();
        assert_eq!("TEST", root_symbol_str);
        assert_eq!("pA", suffix_str);
    }
}
