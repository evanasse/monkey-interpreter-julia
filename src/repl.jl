include("interpreter.jl")

function print_parsererrors(errors::Array{String})
    println("Woops! We ran into some monkey business here!")
    println("  parser errors:")
    for message in errors
        println("\t$(message)")
    end
end

const PROMPT = ">> "

println("Hello! This is the Monkey programming language!")
println("Feel free to type in commands")
print(PROMPT)
input = readline()

env = Environment()

while !isempty(input)
    lexer = Lexer(input)
    parser = Parser(lexer)

    program = parse_program(parser)

    if length(parser.errors) != 0
        print_parsererrors(parser.errors)
    else
        evaluated = eval(program, env)
        if !isnothing(evaluated)
            println(inspect(evaluated))
        end
    end

    print(PROMPT)
    global input = readline()
end

