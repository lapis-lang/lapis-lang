// TODO: RegularLanguage extends KleeneAlgebra
//     https://en.wikipedia.org/wiki/Kleene_algebra

/**
 * 
 */
abstract class RegularLanguage {
    constructor(){}

    /**
     * 
     */
    abstract containsEmpty(): boolean
    
    /**
     * 
     * @param c 
     */
    abstract diff(c: string): RegularLanguage
    
    /**
     * TODO 
     * @param other 
     */
    equals(other: RegularLanguage): boolean {
        return this === other
    }

    abstract height(): number

    /**
     * δ(L) => ∅ if ε ∉ L
     * δ(L) => ε if ε ∈ L
     */
    abstract nullOrEmpty(): RegularLanguage

    /**
     * 
     */
    matches(text: string): boolean {
        return !text ? this.containsEmpty() : this.diff(text[0]).matches(text.substring(1))
    }

    /**
     * 
     */
    protected get _simplifyRules(): Array<(lang: RegularLanguage) => RegularLanguage> {
        return []
    }

    /**
     * 
     */
    simplify(): RegularLanguage {
        return this._simplifyRules.reduce<RegularLanguage>((prev, cur) => {
            return cur(prev)
        }, this)
    }
}

/**
 * A ∪ B
 */
class Alt extends RegularLanguage {
    constructor(readonly left: RegularLanguage, readonly right: RegularLanguage){  super() }

    containsEmpty(): boolean { return this.left.containsEmpty() || this.right.containsEmpty() }

    /**
     * Dc(A ∪ B) => Dc(A) ∪ Dc(B)
     * 
     * @param c 
     */
    diff(c: string): RegularLanguage {
        let simplified = this.simplify()
        return simplified === this ? new Alt(this.left.diff(c), this.right.diff(c)) :
               simplified.diff(c)
    }
    
    height(): number {
        return Math.max(this.left.height(), this.right.height()) + 1
    }

    nullOrEmpty(): RegularLanguage { return new Alt(this.left.nullOrEmpty(), this.right.nullOrEmpty()) }

    /**
     * (A ∪ B) ∪ C = A ∪ (B ∪ C)
     * (A ∪ B) ∪ C = A ∪ (B ∪ C)
     * A ∪ B = B ∪ A
     * L ∪ L = L
     * L+ ∪ ε = L*
     * ∅ ∪ L = L ∪ ∅ = L
     * LM ∪ LN = L(M ∪ N)
     * ML ∪ NL = (M ∪ N)L
     * 
     */
    protected get _simplifyRules(): Array<(lang: RegularLanguage) => RegularLanguage> {
        return [
            (lang: RegularLanguage) =>
                lang instanceof Alt ? 
                    lang.left instanceof Alt ? new Alt(lang.left.left, new Alt(lang.left.right, lang.right)) :
                    lang :
                lang,
            (lang: RegularLanguage) =>
                lang instanceof Alt ?
                    lang.left instanceof Alt ? new Alt(lang.left.left, new Alt(lang.left.right, lang.right)) :
                    lang :
                lang,
            (lang: RegularLanguage) =>
                lang instanceof Alt ? 
                    lang.left.height > lang.right.height ? new Alt(lang.right, lang.left) : lang :
                lang,
            (lang: RegularLanguage) =>
                lang instanceof Alt ?
                    lang.left === lang.right ? lang.left : lang :
                lang,
            (lang: RegularLanguage) =>
                lang instanceof Alt ?
                    lang.left instanceof Plus && lang.right instanceof Empty ? 
                        new Star(lang.left.lang) : lang :
                lang,
            (lang: RegularLanguage) =>
                lang instanceof Alt ?
                    lang.left instanceof Nil ? lang.right :
                    lang.right instanceof Nil ? lang.left :
                    lang :
                lang,
            (lang: RegularLanguage) => 
                lang instanceof Alt && lang.left instanceof Cat && lang.right instanceof Cat ?
                    lang.left.first.equals(lang.right.first) ?  
                        new Cat(lang.left.first, new Alt(lang.left.second, lang.right.second)) :
                    lang.left.second.equals(lang.right.second) ?
                        new Cat(new Alt(lang.left.first, lang.right.first), lang.left.second) : 
                    lang :
                lang
        ]
    }
}

/**
 * A ○ B
 */
class Cat extends RegularLanguage {
    constructor(readonly first: RegularLanguage, readonly second: RegularLanguage){ super() }

    containsEmpty(): boolean { return this.first.containsEmpty() && this.second.containsEmpty() }

    /**
     * Dc(A ○ B) => (Dc(A) ○ B) ∪ (δ(A) ○ Dc(B))
     * 
     * @param c 
     */
    diff(c: string): RegularLanguage {
        return new Alt(
            new Cat(this.first.diff(c), this.second),
            new Cat(this.first.nullOrEmpty(), this.second.diff(c))
        )
    }

    height(): number { return Math.max(this.first.height(), this.second.height()) + 1 }

    nullOrEmpty(): RegularLanguage { return new Cat(this.first.nullOrEmpty(), this.second.nullOrEmpty()) }

    /**
     * (LM)N = L(MN)
     * εL = Lε = L
     * ∅L = L∅ = ∅
     *
     */
    protected get _simplifyRules(): Array<(lang: RegularLanguage) => RegularLanguage> {
        return [
            (lang: RegularLanguage) =>
                lang instanceof Cat  && lang.first instanceof Cat ? 
                    new Cat(lang.first.first, new Cat(lang.first.second, lang.second)) :
                lang,
            (lang: RegularLanguage) => 
                lang instanceof Cat ?
                    lang.first  instanceof Empty ? lang.second :
                    lang.second instanceof Empty ? lang.first  :
                    lang :
                lang,
            (lang: RegularLanguage) => 
                lang instanceof Cat ?
                    lang.first  instanceof Nil ? NIL :
                    lang.second instanceof Nil ? NIL :
                    lang :
                lang
        ]
    }
}

/**
 * 'c'
 */
class Char extends RegularLanguage {
    constructor(readonly value: string) { super() }

    containsEmpty(): boolean { return false }

    /**
     * Dc(c) = ε
     * Dc(c') = ∅ if c is not c'
     * 
     * @param c 
     */
    diff(c: string): RegularLanguage { return c === this.value ? EMPTY : NIL }

    height(): number { return 0 }

    nullOrEmpty(): RegularLanguage { return NIL }

    simplify(): RegularLanguage { return this }
}

/**
 * ε
 */
class Empty extends RegularLanguage {
    containsEmpty(): boolean { return true }

    /**
     * Dc(ε) = ∅
     */
    diff(): RegularLanguage { return NIL }
    
    height(): number { return 0 }
    
    nullOrEmpty(): RegularLanguage { return EMPTY }
    
    simplify(): RegularLanguage { return this }

}
const EMPTY = new Empty()

/**
 * ∅
 */
class Nil extends RegularLanguage {
    containsEmpty(): boolean { return false }
    
    /**
     * Dc(∅) = ∅
     */
    diff(): RegularLanguage { return NIL }

    height(): number { return 0 }

    nullOrEmpty(): RegularLanguage { return NIL }

    simplify(): RegularLanguage { return this }
}
const NIL = new Nil()

/**
 * L*
 */
class Star extends RegularLanguage {
    constructor(readonly lang: RegularLanguage) { super() }

    containsEmpty(): boolean { return true }
    
    /**
     * Dc(L*) => Dc(L) ○ L*
     * 
     * @param c 
     */
    diff(c: string): RegularLanguage { return new Cat(this.lang.diff(c), this.lang) }

    height(): number { return this.lang.height() + 1 }

    nullOrEmpty(): RegularLanguage { return EMPTY }

    /**
     * ∅* = ε
     * ε* = ε
     * L** = L*
     */
    simplify(): RegularLanguage {
        return this.lang instanceof Nil   ? EMPTY :
               this.lang instanceof Empty ? EMPTY :
               this.lang instanceof Star  ? this.lang :
               this
    }
}

/**
 * 
 */
class Opt extends Alt {
    constructor(readonly lang: RegularLanguage) { super(NIL, lang) }

    containsEmpty(): boolean { return this.right.containsEmpty() }

    diff(c: string): RegularLanguage { return new Alt(this.left, this.right.diff(c)) }

    nullOrEmpty(): RegularLanguage { return this.left }

    simplify(): RegularLanguage {
        return new Alt(this.lang, NIL)
    }
}

/**
 * 
 */
class Plus extends Cat {
    constructor(readonly lang: RegularLanguage) { super(lang, new Opt(lang)) }

    simplify(): RegularLanguage {
        return new Cat(this.lang, new Star(this.lang))
    }
}

// helpers for brevity

const choice = (...langs: (RegularLanguage | string)[]): RegularLanguage => 
    langs.reduce((sum: RegularLanguage, next: string | RegularLanguage) => {
        return new Alt(
            sum,
            next instanceof RegularLanguage ? next :
            next.length == 0 ? EMPTY :
            next.length == 1 ? char(next) :
            string(next)
        )
    }, NIL)
const seq = (...langs: (RegularLanguage | string)[]): RegularLanguage => 
    langs.reduce((sum: RegularLanguage, next: string | RegularLanguage) => {
        return new Cat(
            sum,
            next instanceof RegularLanguage ? next :
            next.length == 0 ? EMPTY :
            next.length == 1 ? char(next) :
            string(next)
        )
    }, EMPTY)
const char = (value: string): RegularLanguage => {
    if(value.length != 1) {
        throw new Error("A character must have a length of 1")
    } else {
        return new Char(value)
    }
}
const empty = (): RegularLanguage => EMPTY
const nil = (): RegularLanguage => NIL
const maybe = (lang: RegularLanguage): RegularLanguage => new Opt(lang)
const many = (lang: RegularLanguage): RegularLanguage => new Plus(lang)
const any = (lang: RegularLanguage): RegularLanguage => new Star(lang)
const range = (start: string, end: string): RegularLanguage => {
    if(start.length != 1 || end.length != 1) {
        throw new Error('A range requires strings of length = 1 ')
    } else {
        let [a, b] = [start.charCodeAt(0), end.charCodeAt(0)].sort()
        return start == end ? new Char(start) :
               choice(...Array.from({length: b - a}, (v: number) => new Char(String.fromCharCode(v))))
    }
}

const DIGIT =  range('0', '9')
const string = (value: string): RegularLanguage => 
    value.length == 0 ? EMPTY :
    value.length == 1 ? new Char(value) :
    seq(...value.split(''))

export {choice, seq, char, DIGIT, empty, nil, maybe, many, any, range, string}