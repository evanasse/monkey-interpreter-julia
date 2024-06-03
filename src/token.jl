abstract type TokenType end

struct Token
    type::Type{<:TokenType}
    literal::String

    function Token(type::Type{<:TokenType}, literal::String)
        return new(type, literal)
    end

    function Token()
        return new(TokenType, "")
    end
end

struct ILLEGAL <: TokenType end

# const ILLEGAL = "ILLEGAL"
struct EOF <: TokenType end

# Identifiers + literals
struct IDENT <: TokenType end
struct INT <: TokenType end
struct STR <: TokenType end

# Operators
struct ASSIGN <: TokenType end
struct PLUS <: TokenType end
struct MINUS <: TokenType end
struct BANG <: TokenType end
struct ASTERISK <: TokenType end
struct SLASH <: TokenType end
struct LT <: TokenType end
struct GT <: TokenType end
struct EQ <: TokenType end
struct NOT_EQ <: TokenType end

# Delimiters
struct COMMA <: TokenType end
struct SEMICOLON <: TokenType end
struct COLON <: TokenType end

struct LPAREN <: TokenType end
struct RPAREN <: TokenType end
struct LBRACE <: TokenType end
struct RBRACE <: TokenType end
struct LBRACKET <: TokenType end
struct RBRACKET <: TokenType end

# Keywords
struct FUNCTION <: TokenType end
struct LET <: TokenType end
struct TRUE <: TokenType end
struct FALSE <: TokenType end
struct IF <: TokenType end
struct ELSE <: TokenType end
struct RETURN <: TokenType end

const keywords = Dict(
    "fn" => FUNCTION,
    "let" => LET,
    "true" => TRUE,
    "false" => FALSE,
    "if" => IF,
    "else" => ELSE,
    "return" => RETURN
)

function lookupident(ident::String)
    if haskey(keywords, ident)
        return keywords[ident]
    end

    return IDENT
end
