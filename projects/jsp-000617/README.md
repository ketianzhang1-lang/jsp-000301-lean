# JSP-000617 / Erdos 749: upper-density formalization development

**Research branch, not a completed proof or prize submission.**

Target: for every real epsilon > 0, construct a set A of natural numbers whose
sumset has upper asymptotic density at least 1-epsilon and whose ordered additive
representation function is bounded by a constant depending only on epsilon.
The lower-density original problem is a different target and is not claimed.

The mathematical upper-density result is attributed to Aron Bhalla, with disclosed
GPT-5.4 assistance, on the original problem page. The finite-field/parabola and
widely separated scale architecture is explained by Terence Tao in the discussion.
These authors and Mathlib contributors retain their credit. This repository's
implementation is prepared with OpenAI ChatGPT assistance. No mathematical novelty,
first-formalization priority, organizer review, eligibility or payment is asserted.

Sources:
- https://www.erdosproblems.com/749
- https://www.erdosproblems.com/forum/thread/749
- https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000617

Initial work: algebraic uniqueness of unordered parabola representations, a bound
of two ordered representations, and the corresponding finite sumset lower bound.
The global near-full-density construction and infinite-scale gluing are not yet
implemented. Passing this module's CI must not be described as completing Erdos 749
or its upper-density variant. No official PR should be opened for these lemmas alone.

Public official issue/PR searches for the JSP number and Erdos 749 returned no
matches on 2026-09-16. Public search is incomplete; it cannot certify global priority.

Toolchain: Lean/Mathlib 4.34.0, with the committed dependency manifest copied from the
previous verified project and renamed without changing dependency revisions.
