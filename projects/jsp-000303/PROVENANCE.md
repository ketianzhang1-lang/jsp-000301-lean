# Sources and scope

## Problem and statement

- [Official JSP-000303 catalog](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000303).
  The record is Open, Lean proof No, Eligible to claim No. This contribution
  does not change or override that record.
- [Erdős Problem 367](https://www.erdosproblems.com/367), originally associated
  with Erdős and Graham, *Old and New Problems and Results in Combinatorial
  Number Theory* (1980).
- [Formal Conjectures specification](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/367.lean).
  `Statement.lean` retains its Apache-2.0 notice. It transcribes the exact `B`
  definition and the types of `erdos_367.variants.k_ge_three_lower` and
  `erdos_367.parts.ii`, omitting research annotations and replacing
  `answer(False)` with `False`. Only proved results are included.

## Mathematical and formalization attribution

- Wouter van Doorn: [original discussion](https://www.erdosproblems.com/forum/thread/367#post-1766).
- Terence Tao: [Pell construction discussion](https://www.erdosproblems.com/forum/thread/367#post-1776).
- [Earlier Lean implementation](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos367b.lean).
  Its header credits Wouter van Doorn, Terence Tao and Gemini Deepthink for
  informal work, and Aristotle and Boris Alexeev for formalization. All these
  credits are preserved here. The earlier source was reviewed before writing
  this implementation. No ownership or priority over that work is asserted.

| Inspected earlier endpoint | This package |
| --- | --- |
| Maximum powerful divisor as definition | Exact prime-factorization product from Formal Conjectures |
| Pell witness and `n(n+1)5^t` bound | New integer recurrence and ring lifting proof |
| No universal constant for all natural n | Failure of the eventual Big-O bound, for every k >= 3 |
| Logarithmic growth claim in explanatory mathematics | Kernel-checked `log(n_t) <= 6*5^(t+1)` and explicit constant 1/6 |

The same classical construction underlies both packages. This is an incremental
formalization contribution. No new solution of the open upper-bound question,
sharp constant, classification of all witnesses, or higher-full-part result
is claimed. Global first-formalization priority has not been established.

On the submission-date check, searching the official repository for JSP-000303
and Erdős 367 did not locate a competing problem-specific PR. This limited
search is not evidence of global priority; the public earlier Lean proof exists.

## Assistance, identity and verification

OpenAI ChatGPT assisted mathematical review, new Lean code, execution and
packaging. Proposed recipient: `RECIPIENT-JSP-000303-KZ-A`, confirmation pending.
No private contact or payment information is included. Contributor-run kernel
and independent-implementation checks do not constitute organizer certification.
