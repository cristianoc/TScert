/** A dependency worklist for flow rules over growing facts.
 * A transfer registers the facts it reads and reports the facts it grows.
 * Set inclusions can then copy only the tokens added to their source. */
type Fact = object | string;
export type FlowRule = () => void;

/** A growing set stored by the solver. Transient sets have no copy cursor. */
export class FlowTokens implements Iterable<number> {
  private readonly tokens: Set<number>;
  private added?: number[];
  private copies?: WeakMap<FlowTokens, number>;

  constructor(tokens: Iterable<number> = []) {
    this.tokens = new Set(tokens);
  }

  get size(): number { return this.tokens.size; }
  has(token: number): boolean { return this.tokens.has(token); }
  [Symbol.iterator](): SetIterator<number> { return this.tokens.values(); }

  add(token: number): void {
    const before = this.tokens.size;
    this.tokens.add(token);
    if (this.tokens.size > before) this.added?.push(token);
  }

  *since(start: number): Iterable<number> {
    if (start === this.size) return;
    const added = this.added ??= [...this.tokens];
    for (let i = start; i < added.length; i++) {
      const token = added[i];
      if (token !== undefined) yield token;
    }
  }

  copyFrom(source: FlowTokens): void {
    const copies = this.copies ??= new WeakMap();
    const start = copies.get(source) ?? 0;
    if (start === source.size) return;
    for (const token of source.since(start)) this.add(token);
    copies.set(source, source.size);
  }
}
/** A rule reads dependencies as it runs, including those discovered through
 * new tokens. Only growth of a dependency schedules its readers. */
export class FlowWorklist {
  private readonly readers = new Map<Fact, Set<FlowRule>>();
  private pending = new Set<FlowRule>();
  private readonly grown = new Set<Fact>();
  private deferred = new Set<FlowRule>();
  private runningDeferred = false;
  private current: FlowRule | null = null;

  get active(): boolean { return this.current !== null; }

  read(fact: Fact): void {
    if (this.current === null) return;
    let readers = this.readers.get(fact);
    if (!readers) this.readers.set(fact, readers = new Set());
    readers.add(this.current);
  }

  grow(fact: Fact): void {
    if (this.current !== null && this.readers.has(fact)) this.grown.add(fact);
  }

  add(rule: FlowRule): void {
    this.pending.add(rule);
  }

  /** Evaluate a rule and register its reads against that rule. */
  run(rule: FlowRule): void {
    const parent = this.current;
    this.current = rule;
    try {
      rule();
    } finally {
      this.current = parent;
    }
  }

  /** Revisit the current rule at quiescence. While draining deferred rules,
   * the caller can apply the transfer that required quiescence. */
  defer(): boolean {
    if (this.current === null || this.runningDeferred) return false;
    this.deferred.add(this.current);
    return true;
  }

  solve(beforeRule: () => void): void {
    while (this.pending.size > 0 || this.deferred.size > 0) {
      this.runningDeferred = this.pending.size === 0;
      const ready = this.runningDeferred ? this.deferred : this.pending;
      if (this.runningDeferred) this.deferred = new Set();
      else this.pending = new Set();
      for (const rule of ready) {
        beforeRule();
        this.run(rule);
      }
      for (const fact of this.grown)
        for (const rule of this.readers.get(fact) ?? []) this.pending.add(rule);
      this.grown.clear();
    }
    this.current = null;
    this.readers.clear();
  }
}
