package main

//:: ExpectedOutput(parser_error)
const i := 10
const j int := 10

type A := int

func main() {
    var a := 10
    var b int := 10
}