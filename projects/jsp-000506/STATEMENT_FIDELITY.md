# Original-statement correspondence

The original question asks whether the chromatic number minus the cochromatic
number of `G(n,1/2)` diverges with probability tending to one as `n` tends to
infinity. The full statement is understood in its standard random-graph
sense: every fixed finite gap threshold is met with probability tending to
one. We do not assert a pathwise almost-sure limit under an unspecified
coupling of graphs of all orders.

## Exact finite model

Our `Edge n` consists of pairs `(u,v)` of vertices in `Fin n` with `u < v`.
Every simple undirected labelled graph corresponds to exactly one subset of
this edge type. `graphEquiv n` proves this bijection with Mathlib's
`SimpleGraph (Fin n)`, including orders zero and one. The graph contains no
loops and treats the two orders of an edge as the same undirected edge.

`Proper s k` represents a proper colouring with at most `k` colours.
`CoProper s k` permits each colour class to be either an independent set or
a clique. Empty classes are allowed and do not change the minimum. The
correspondence of both predicates and both minima is proved in
`JSP000506Bridge.lean`; it is not inferred from similarly named definitions.

`mass A` is the exact rational `A.card / 2^(Fintype.card (Edge n))`.
`mass_event_eq_randomGraph` proves that its real cast equals the probability
under Mathlib's binomial graph law at edge probability one half. All events
are measurable on these finite spaces. Uniform counting thus means
independently selecting every possible edge with probability one half.

The finite source uses natural subtraction `chi s - zeta s`. Since
`zeta_le_chi` holds for every graph, `gap_cast_eq` proves that its real cast
is the literal real difference in the quantitative source. No truncation
changes the event.

## Complete endpoint and quantitative dependence

`JSP000506.jsp_000506` states, for every natural `g`, that

```text
lim[n -> infinity]
  mass {s : Finset (Edge n) | g <= chi s - zeta s} = 1.
```

The limit runs along all natural graph orders. It is not restricted to an
infinite subsequence, a density-one set of orders, or selected finite orders.
`fixed_threshold_tendsto_one` also permits every real fixed threshold.
`small_gap_probability_tendsto_zero` proves the equivalent vanishing
probability of `chi - zeta <= g` for every fixed natural width.

The quantitative dependency is Samuil Petkov's theorem with

```text
C = (log 2)^2 / 4 * log (200 / 153) > 0,
scale(n) = C * n / (log n)^3.
```

We retain that exact positive constant, prove that the scale diverges, and
transfer its probability limit to our original counting model. More generally,
`threshold_tendsto_one` handles every deterministic real threshold function
eventually bounded by this scale, without a monotonicity assumption.
Small-order values of the logarithmic expression do not affect the limit.

## Relationship to the earlier finite theorem

`heckel_proposition3` is retained for every natural `n` and `g`, with its
original hypothesis that a small gap has probability at least 999/1000.
The new complete endpoint has no such hypothesis. In fact,
`eventually_not_heckel_premise` shows that this premise eventually fails for
every fixed `g`. `complete_package` combines the complete asymptotic theorem
with the retained finite theorem without treating the latter as a proof of
the asymptotic result.

The finer phase-dependent refinement discussed in Petkov's manuscript is
outside the imported Lean claim and outside this submission. It is not
needed for either the displayed quantitative bound or the original problem.
