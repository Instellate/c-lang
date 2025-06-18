use std::iter::Peekable;
use std::str::Chars;

pub struct Tokenizer<'a> {
    chars: Peekable<Chars<'a>>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Token {
    EOF,
    Identifier(String),
    Integer(String),
    String(String),
    Operator(&'static str),
    Semicolon,
    Comma,
    Ampersand,
    BraceOpen,
    BraceClose,
    ParenOpen,
    ParenClose,
    SquareBracketOpen,
    SquareBracketClose,
    AngleBracketOpen,
    AngleBracketClose,
    ConstKeyword,
    ReturnKeyword,
    ExternKeyword,
    IfKeyword,
    ElseKeyword,
    VarArgument,
    Invalid,
}

impl Token {
    pub fn is_identifier(&self) -> bool {
        if let Self::Identifier(_) = self {
            true
        } else {
            false
        }
    }

    pub fn is_integer(&self) -> bool {
        if let Self::Integer(_) = self {
            true
        } else {
            false
        }
    }

    pub fn is_string(&self) -> bool {
        if let Self::String(_) = self {
            true
        } else {
            false
        }
    }

    pub fn is_operator(&self) -> bool {
        if let Self::Operator(_) = self {
            true
        } else {
            false
        }
    }
}

impl<'a> Tokenizer<'a> {
    pub fn new<T: AsRef<str>>(s: &'a T) -> Self {
        Self {
            chars: s.as_ref().chars().peekable(),
        }
    }

    fn next_char(&mut self) -> Option<char> {
        self.chars.next()
    }

    fn peek_char(&mut self) -> Option<char> {
        self.chars.peek().map(|c| c.clone())
    }

    fn peek_is(&mut self, chr: char) -> bool {
        self.peek_char().map(|c| c == chr).unwrap_or(false)
    }

    /// Consumes whitespace and comments
    fn consume_whitespace(&mut self) {
        while self
            .chars
            .peek()
            .map(|c| c.is_whitespace())
            .unwrap_or(false)
        {
            self.next_char();
        }

        let mut cloned = self.chars.clone();
        cloned.next();
        if self.chars.peek().map(|c| *c == '/').unwrap_or(false)
            && cloned.peek().map(|c| *c == '/').unwrap_or(false)
        {
            while self.chars.peek().map(|c| *c != '\n').unwrap_or(false) {
                self.next_char();
            }
            self.next_char();
        }
    }

    /// Consumes alphanumeric characters until non-alphanumeric character is hit.
    fn consume_characters(&mut self) -> Option<String> {
        let mut string = String::new();

        let mut peek = self.peek_char()?;
        while peek.is_alphanumeric() {
            string.push(self.next_char()?);

            if let Some(pk) = self.peek_char() {
                peek = pk
            } else {
                return Some(string);
            }
        }

        Some(string)
    }

    /// Consumes and parses a integer
    fn consume_integer(&mut self) -> Option<String> {
        let mut string = String::new();

        let mut peek = self.peek_char()?;
        while peek.is_numeric() {
            string.push(self.next_char()?);

            if let Some(pk) = self.peek_char() {
                peek = pk;
            } else {
                return Some(string);
            }
        }

        Some(string)
    }

    fn consume_string(&mut self) -> Option<String> {
        let mut string = String::new();

        self.next_char();
        while !self.peek_is('"') {
            string.push(self.next_char()?)
        }
        self.next_char();

        Some(string)
    }

    pub fn next_token(&mut self) -> Token {
        self.internal_next_token().unwrap_or_else(|| Token::EOF)
    }

    pub fn peek_token(&self) -> Token {
        Self {
            chars: self.chars.clone(),
        }
        .next_token()
    }

    fn internal_next_token(&mut self) -> Option<Token> {
        self.consume_whitespace();

        let peek = self.peek_char()?;
        if peek.is_alphabetic() {
            let string = self.consume_characters()?;

            match string.as_str() {
                "const" => Some(Token::ConstKeyword),
                "return" => Some(Token::ReturnKeyword),
                "extern" => Some(Token::ExternKeyword),
                "if" => Some(Token::IfKeyword),
                "else" => Some(Token::ElseKeyword),
                _ => Some(Token::Identifier(string)),
            }
        } else if peek == '-' {
            self.next_char()?;
            if self.chars.peek().map(|c| c.is_numeric()).unwrap_or(false) {
                let integer = format!("-{}", self.consume_integer()?);
                Some(Token::Integer(integer))
            } else {
                Some(Token::Operator("-"))
            }
        } else if peek.is_numeric() {
            Some(Token::Integer(self.consume_integer()?))
        } else if peek == '"' {
            Some(Token::String(self.consume_string()?))
        } else if peek == '.' {
            for _ in 0..3 {
                if !self.peek_is('.') {
                    return Some(Token::Invalid);
                }
                self.chars.next()?;
            }
            Some(Token::VarArgument)
        } else {
            self.next_char()?;
            match peek {
                '=' => {
                    if self.peek_is('=') {
                        self.next_char()?;
                        Some(Token::Operator("=="))
                    } else {
                        Some(Token::Operator("="))
                    }
                }
                '*' => Some(Token::Operator("*")),
                '/' => Some(Token::Operator("/")),
                '+' => Some(Token::Operator("+")),
                '-' => Some(Token::Operator("-")),
                '{' => Some(Token::BraceOpen),
                '}' => Some(Token::BraceClose),
                '(' => Some(Token::ParenOpen),
                ')' => Some(Token::ParenClose),
                '[' => Some(Token::SquareBracketOpen),
                ']' => Some(Token::SquareBracketClose),
                ';' => Some(Token::Semicolon),
                ',' => Some(Token::Comma),
                '&' => Some(Token::Ampersand),
                '%' => Some(Token::Operator("%")),
                _ => None,
            }
        }
    }
}
