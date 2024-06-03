import Base.get

abstract type ObjectType end

struct INTEGER <: ObjectType end
struct STRING <: ObjectType end
struct BOOLEAN <: ObjectType end
struct NULL <: ObjectType end
struct RETURN_VALUE <: ObjectType end
struct ERROR <: ObjectType end
struct ARRAY <: ObjectType end
struct FUNC <: ObjectType end
struct BUILTIN <: ObjectType end
struct HASH <: ObjectType end

abstract type Object end


struct MonkeyInteger <: Object
    value::Int
end

function inspect(i::MonkeyInteger)
    string(i.value)
end

function type(::MonkeyInteger)
    INTEGER
end




struct MonkeyBoolean <: Object
    value::Bool
end

function inspect(b::MonkeyBoolean)
    string(b.value)
end

function type(::MonkeyBoolean)
    BOOLEAN
end




struct MonkeyString <: Object
    value::String
end

function inspect(s::MonkeyString)
    s.value
end

function type(::MonkeyString)
    STRING
end




struct MonkeyNull <: Object end

function inspect(::MonkeyNull)
    "null"
end

function type(::MonkeyNull)
    NULL
end




struct MonkeyReturnValue <: Object
    value::Object
end

function inspect(rv::MonkeyReturnValue)
    inspect(rv.value)
end

function type(::MonkeyReturnValue)
    RETURN_VALUE
end




struct MonkeyError <: Object
    message::String
end

function inspect(e::MonkeyError)
    "ERROR: $(e.message)"
end

function type(::MonkeyError)
    ERROR
end




struct MonkeyArray <: Object
    elements::Array{Object}
end

function inspect(a::MonkeyArray)
    elements = map(inspect, a.elements) |> elements -> join(elements, ", ")

    "[$(elements)]"
end

function type(::MonkeyArray)
    ARRAY
end




struct MonkeyBuiltin <: Object
    func::Function
end

function inspect(b::MonkeyBuiltin)
    "builtin function"
end

function type(::MonkeyBuiltin)
    BUILTIN
end








struct Environment
    store::Dict{String,Object}
    outer::Union{Environment,Nothing}
end

function Environment()
    Environment(Dict{String,Object}(), nothing)
end

function Environment(outer::Environment)
    Environment(Dict{String,Object}(), outer)
end


function get(env::Environment, name::String)
    obj = get(env.store, name, nothing)

    if isnothing(obj) && !isnothing(env.outer)
        obj = get(env.outer, name)
    end

    obj
end

function set(env::Environment, name::String, value::Object)
    env.store[name] = value

    value
end


const builtins = Dict(
    "len" => MonkeyBuiltin(
        function (args::Object...)
            if length(args) != 1
                return MonkeyError("wrong number of arguments. got=$(length(args)), want=1")
            end

            if typeof(args[1]) == MonkeyString
                return MonkeyInteger(length(args[1].value))
            elseif typeof(args[1]) == MonkeyArray
                return MonkeyInteger(length(args[1].elements))
            else
                return MonkeyError("argument to 'len' not supported, got $(type(args[1]))")
            end
        end
    ),
    "first" => MonkeyBuiltin(
        function (args::Object...)
            if length(args) != 1
                return MonkeyError("wrong number of arguments. got=$(length(args)), want=1")
            end

            if typeof(args[1]) != MonkeyArray
                return MonkeyError("argument to 'first' not supported, got $(type(args[1]))")
            end

            if length(args[1].elements) > 0
                return args[1].elements[1]
            end

            MONKEY_NULL
        end
    ),
    "last" => MonkeyBuiltin(
        function (args::Object...)
            if length(args) != 1
                return MonkeyError("wrong number of arguments. got=$(length(args)), want=1")
            end

            if typeof(args[1]) != MonkeyArray
                return MonkeyError("argument to 'last' not supported, got $(type(args[1]))")
            end

            len = length(args[1].elements)
            if len > 0
                return args[1].elements[len]
            end

            MONKEY_NULL
        end
    ),
    "rest" => MonkeyBuiltin(
        function (args::Object...)
            if length(args) != 1
                return MonkeyError("wrong number of arguments. got=$(length(args)), want=1")
            end

            if typeof(args[1]) != MonkeyArray
                return MonkeyError("argument to 'rest' not supported, got $(type(args[1]))")
            end


            len = length(args[1].elements)
            if len > 0
                return MonkeyArray(args[1].elements[2:len])
            end

            MONKEY_NULL
        end
    ),
    "push" => MonkeyBuiltin(
        function (args::Object...)
            if length(args) != 2
                return MonkeyError("wrong number of arguments. got=$(length(args)), want=2")
            end

            if typeof(args[1]) != MonkeyArray
                return MonkeyError("argument to 'push' must be ARRAY, got $(type(args[1]))")
            end

            MonkeyArray(push!(args[1].elements, args[2]))
        end
    ),
    "puts" => MonkeyBuiltin(
        function (args::Object...)
            for arg in args
                println(inspect(arg))
            end

            MONKEY_NULL
        end
    )
)

struct HashKey
    type::Union{Type{STRING},Type{INTEGER},Type{BOOLEAN}}
    value::UInt
end

function hashkey(s::MonkeyString)
    HashKey(type(s), UInt(hash(s.value)))
end

function hashkey(i::MonkeyInteger)
    HashKey(type(i), UInt(i.value))
end

function hashkey(b::MonkeyBoolean)
    value::UInt = 0

    if b.value
        value = 1
    end

    HashKey(type(b), value)
end
