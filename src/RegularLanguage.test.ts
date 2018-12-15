import {any, seq,maybe,many,char,DIGIT, choice, range} from "./RegularLanguage"

// -?[0...9]+
let integerNumber = seq(maybe(char('-')), many(DIGIT))

let lower = range('a','z')
let upper = range('A', 'Z')
let alpha = choice(lower, upper)

let ident = seq(alpha, any(seq(alpha, DIGIT)))