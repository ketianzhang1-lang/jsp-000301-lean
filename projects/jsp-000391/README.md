# JSP-000391 / Erdos 482: general-base digit recurrence

New, independent development. This project is unrelated to the submitted JSP-000390 and the discontinued JSP-000617 project; neither is modified by this branch.

Target: formalize Thomas Stoll's Theorem 1.3 from *On Families of Nonlinear Recurrences Related to Digits*, Journal of Integer Sequences 8 (2005), Article 05.3.2. The intended theorem covers every radix g >= 2, every normalized real 1 <= t < g, every shift in the published admissible interval, and every digit index. Mathematical credit remains with Stoll and the earlier literature; OpenAI ChatGPT assisted this independently written Lean implementation. No mathematical novelty, first-formalization priority, or award is asserted.

Status: development; consult actual CI results. Full positive-real normalization and a final source-bound verification package are still being completed. Do not submit unfinished development as a verified prize claim.

References:
- https://www.erdosproblems.com/482
- https://cs.uwaterloo.ca/journals/JIS/VOL8/Stoll/stoll56.html
- https://cs.uwaterloo.ca/journals/JIS/VOL8/Stoll/stoll56.pdf
- https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000391

Index convention: sequence(0) is the paper's u_1. digit(0) is the leading significant digit, not the first fractional digit. The main proof must come from the recursive floor definition and not from redefining the sequence as its proposed closed form.
