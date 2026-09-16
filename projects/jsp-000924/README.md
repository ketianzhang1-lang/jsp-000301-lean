# JSP-000924 / Erdos 1113: fourth-power Sierpinski family

Research contribution for the known construction, not a resolution of the open
question about absence of every finite prime covering set. Do not submit until
actual build, axiom and external-checker evidence has been obtained.

The target is the entire explicit family
(734110615000775 + 36893488147419103230*j)^4, for every natural j.
Each is a positive odd Sierpinski number for all natural exponents, including zero.
The proof combines a partial congruence cover with the Sophie Germain identity.
It also proves infinitude and failure of the particular standard seven-prime list.
It does not show that any member has no OTHER finite prime cover.

Mathematical attribution: Anatoly S. Izotov (1995), A Note on Sierpinski Numbers,
Fibonacci Quarterly 33(3), 206-207; Michael Filaseta, Carrie Finch and Mark Kozek
(2008), On powers associated with Sierpinski numbers, Riesel numbers and Polignac's
conjecture, Journal of Number Theory 128, 1916-1940, Section 2, explicit progression.
The 1995 and 2008 constructions interchange the roles of 641 and 6700417; this
implementation uses the 2008 progression and its verified residues, not a literal
transcription of the different residue choices in the 1995 theorem.

Sources:
- https://www.erdosproblems.com/1113
- https://www.fq.math.ca/Scanned/33-3/izotov.pdf
- https://people.math.sc.edu/filaseta/papers/SierpinskiEtCoPapNew.pdf

Independently written Lean code with OpenAI ChatGPT assistance under the submitting
account's direction. No new mathematics, global priority, organizer approval,
confirmed recipient or prize entitlement is claimed. Earlier submitted projects
and the abandoned JSP-000617 work are not modified.
