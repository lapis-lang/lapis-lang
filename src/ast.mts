/**
 * Lapis language AST — class-based hierarchy.
 *
 * Every node carries a `span` property ({start, end} in character offsets)
 * populated directly from the `Span` argument passed to each `.map()` callback
 * in the grammar. Line/column information is derived lazily via the `Module`
 * root's `positionOf(offset)` helper.
 */

import type { Span } from '@lapis-lang/derivative-parser';

// ── Base ─────────────────────────────────────────────────────────────────────

export abstract class Node {
    constructor(readonly span: Span) {}
}

// ── Literals ─────────────────────────────────────────────────────────────────

export class IntLit extends Node {
    constructor(readonly value: number, span: Span) { super(span); }
}

export class StringLit extends Node {
    constructor(readonly value: string, span: Span) { super(span); }
}

export class SymbolLit extends Node {
    constructor(readonly name: string, span: Span) { super(span); }
}

// ── References ───────────────────────────────────────────────────────────────

/** camelCase identifier / operation name */
export class Ident extends Node {
    constructor(readonly name: string, span: Span) { super(span); }
}

/** PascalCase variant or type name */
export class VariantRef extends Node {
    constructor(readonly name: string, span: Span) { super(span); }
}

export class SelfRef extends Node {
    constructor(span: Span) { super(span); }
}

export class FamilyRef extends Node {
    constructor(span: Span) { super(span); }
}

export class CoSelfRef extends Node {
    constructor(span: Span) { super(span); }
}

/** `old fieldName` — raw pre-fold sub-node (paramorphism) */
export class OldRef extends Node {
    constructor(readonly fieldName: string, span: Span) { super(span); }
}

/** `prev fieldName` — previous fold result (histomorphism) */
export class PrevRef extends Node {
    constructor(readonly fieldName: string, span: Span) { super(span); }
}

/** `aux foldName` — auxiliary fold result (zygomorphism) */
export class AuxRef extends Node {
    constructor(readonly foldName: string, span: Span) { super(span); }
}

// ── Composite expressions ────────────────────────────────────────────────────

/** `[params | body]` — first-class block / lambda */
export class Block extends Node {
    constructor(
        readonly params: Ident[],
        readonly body: Node,
        span: Span,
    ) { super(span); }
}

/** `(key: val, ...)` — inline record / named-argument record */
export class RecordEntry extends Node {
    constructor(
        readonly key: string,
        readonly value: Node,
        span: Span,
    ) { super(span); }
}

export class Record extends Node {
    constructor(readonly entries: RecordEntry[], span: Span) { super(span); }
}

/** `{ expr, ... }` — array literal */
export class ArrayLit extends Node {
    constructor(readonly items: Node[], span: Span) { super(span); }
}

// ── Binary / unary operations ─────────────────────────────────────────────────

export class BinarySend extends Node {
    constructor(
        readonly receiver: Node,
        readonly op: string,
        readonly arg: Node,
        span: Span,
    ) { super(span); }
}

export class UnarySend extends Node {
    constructor(
        readonly receiver: Node,
        readonly selector: string,
        span: Span,
    ) { super(span); }
}

/**
 * `receiver key1: arg1 key2: arg2 ...`
 * Smalltalk-style multi-keyword message send.
 */
export class KeywordSend extends Node {
    constructor(
        readonly receiver: Node,
        readonly selectorParts: string[],
        readonly args: Node[],
        span: Span,
    ) { super(span); }
}

export class PrefixSend extends Node {
    constructor(
        readonly op: string,
        readonly operand: Node,
        span: Span,
    ) { super(span); }
}

// ── Spec ─────────────────────────────────────────────────────────────────────

/**
 * `<key: val, key: val, ...>` — fold/unfold/map specification record.
 * keys: e.g. 'in', 'out', 'para', 'histo', 'aux', 'properties', 'typeParam'
 */
export class Spec extends Node {
    constructor(readonly entries: SpecEntry[], span: Span) { super(span); }
}

export class SpecEntry extends Node {
    constructor(
        readonly key: string,
        readonly value: Node | null,   // null for boolean flags like `para`, `histo`
        span: Span,
    ) { super(span); }
}

// ── Contract clauses ──────────────────────────────────────────────────────────

export type ContractKind = 'invariant' | 'demands' | 'ensures' | 'rescue';

export class ContractClause extends Node {
    constructor(
        readonly kind: ContractKind,
        readonly block: Block,
        span: Span,
    ) { super(span); }
}

// ── Field declarations ────────────────────────────────────────────────────────

export class Field extends Node {
    constructor(
        readonly name: string,         // camelCase field name
        readonly typeName: string | null,    // PascalCase type annotation, or null
        span: Span,
    ) { super(span); }
}

// ── Variant declaration ───────────────────────────────────────────────────────

export class Variant extends Node {
    constructor(
        readonly name: string,              // PascalCase
        readonly fields: Field[],
        readonly invariants: ContractClause[],
        span: Span,
    ) { super(span); }
}

// ── Case arm (fold/unfold body) ───────────────────────────────────────────────

export class CaseArm extends Node {
    constructor(
        readonly pattern: string,           // PascalCase variant name
        readonly bindings: string[],        // field binding names (camelCase or '_')
        readonly body: Node,
        span: Span,
    ) { super(span); }
}

// ── Satisfies clause ──────────────────────────────────────────────────────────

export class Satisfies extends Node {
    constructor(readonly protocolName: string, span: Span) { super(span); }
}

// ── Sub-declarations ──────────────────────────────────────────────────────────

export class FoldDecl extends Node {
    constructor(
        readonly name: string,
        readonly spec: Spec | null,
        readonly contractClauses: ContractClause[],
        readonly arms: CaseArm[],
        span: Span,
    ) { super(span); }
}

export class UnfoldDecl extends Node {
    constructor(
        readonly name: string,       // PascalCase constructor name
        readonly spec: Spec | null,
        readonly arms: CaseArm[],
        span: Span,
    ) { super(span); }
}

export class MapDecl extends Node {
    constructor(
        readonly name: string,
        readonly spec: Spec | null,
        readonly transform: Block,
        span: Span,
    ) { super(span); }
}

export class MergeDecl extends Node {
    constructor(
        readonly name: string,
        readonly foldNames: string[],   // e.g. ['#double', '#sum']
        span: Span,
    ) { super(span); }
}

// ── Top-level declarations ────────────────────────────────────────────────────

export type DataBodyItem =
    | Variant
    | FoldDecl
    | UnfoldDecl
    | MapDecl
    | MergeDecl
    | Satisfies;

export class DataDecl extends Node {
    constructor(
        readonly name: string,
        readonly parent: string | null,   // <: ParentName
        readonly body: DataBodyItem[],
        span: Span,
    ) { super(span); }
}

export type BehaviorBodyItem =
    | FoldDecl
    | UnfoldDecl
    | MapDecl
    | MergeDecl;

export class BehaviorDecl extends Node {
    constructor(
        readonly name: string,
        readonly parent: string | null,
        readonly observers: Field[],     // declared observer signatures
        readonly body: BehaviorBodyItem[],
        span: Span,
    ) { super(span); }
}

export type ProtocolBodyItem = FoldDecl;  // methods (abstract or with default body)

export class ProtocolDecl extends Node {
    constructor(
        readonly name: string,
        readonly parent: string | null,
        readonly methods: ProtocolBodyItem[],
        span: Span,
    ) { super(span); }
}

export class RelationDecl extends Node {
    constructor(
        readonly name: string,
        readonly variants: Variant[],
        readonly folds: FoldDecl[],
        span: Span,
    ) { super(span); }
}

export class QueryDecl extends Node {
    constructor(
        readonly name: string,
        readonly observers: Field[],
        readonly unfolds: UnfoldDecl[],
        span: Span,
    ) { super(span); }
}

export class IoDecl extends Node {
    constructor(
        readonly name: string,
        readonly stateFields: Field[],
        readonly arms: CaseArm[],
        span: Span,
    ) { super(span); }
}

// ── Module root ───────────────────────────────────────────────────────────────

export type TopLevelDecl =
    | DataDecl
    | BehaviorDecl
    | ProtocolDecl
    | RelationDecl
    | QueryDecl
    | IoDecl;

export class Module extends Node {
    /** Precomputed line-start offsets for O(log n) line/column lookup. */
    private readonly _lineOffsets: number[];

    constructor(
        readonly declarations: TopLevelDecl[],
        readonly source: string,
        span: Span,
    ) {
        super(span);
        this._lineOffsets = Module._buildLineOffsets(source);
    }

    private static _buildLineOffsets(source: string): number[] {
        const offsets = [0];
        for (let i = 0; i < source.length; i++) {
            if (source[i] === '\n') offsets.push(i + 1);
        }
        return offsets;
    }

    /** Convert a 0-based character offset to 1-based line and column. */
    positionOf(offset: number): { line: number; column: number } {
        let lo = 0;
        let hi = this._lineOffsets.length - 1;
        while (lo < hi) {
            const mid = (lo + hi + 1) >> 1;
            if (this._lineOffsets[mid]! <= offset) lo = mid;
            else hi = mid - 1;
        }
        return { line: lo + 1, column: offset - this._lineOffsets[lo]! + 1 };
    }
}
