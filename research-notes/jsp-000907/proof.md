# An odd-rim construction of 4-critical graphs with at most five chords per cycle

**Date:** 17 September 2026  
**Status:** Candidate research note. This is not Lean-verified, does not claim first-solution priority, and addresses the second question of Erdős Problem 1091 rather than the whole JSP-000907 entry.

## Prior work and scope

The first question of Erdős Problem 1091 asks whether every $K_4$-free 4-chromatic graph has an odd cycle with at least two chords; this was answered affirmatively by Voss and is not reproved here. The second asks whether there is a function $f(r)\to\infty$ such that every 4-chromatic graph whose subgraphs on at most $r$ vertices are 3-colorable contains an odd cycle with at least $f(r)$ chords. Alexeev--Putterman--Sawhney--Sellke--Valiant already answered that question negatively using arbitrarily large 4-critical graphs with at most ten chords in every cycle. The construction below gives a simpler family with at most five chords in every cycle and at most four in every odd cycle. Novelty over all literature is not established.

## Construction

Let $\ell\ge3$ be odd, with indices modulo $\ell$. Define $G_\ell$ on

$$V(G_\ell)=\{z\}\cup\{v_i,a_i,b_i,c_i:0\le i<\ell\}.$$

For each $i$, include precisely the seven edges

$$v_i v_{i+1},\quad v_i a_i,\quad a_i b_i,\quad a_i c_i,\quad b_i c_i,\quad z b_i,\quad z c_i.$$

There are no other edges.

## Theorem

For every odd $\ell\ge3$:

1. $G_\ell$ has $4\ell+1$ vertices and $7\ell$ edges, is $K_4$-free, and has chromatic number four.
2. Every proper subgraph of $G_\ell$ is 2-degenerate; hence $G_\ell$ is 4-critical.
3. Every simple cycle has at most five chords.
4. Every odd simple cycle has at most four chords.
5. Both bounds are attained in this family.

### Chromatic number

Every non-$z$ vertex has degree three and $G_\ell-z$ is connected. Suppose a 3-coloring exists and give $z$ color 0. Since $b_i,c_i$ are adjacent to each other and to $z$, they use the other two colors, so $a_i$ must have color 0. Thus every $v_i$ must avoid color 0, forcing a 2-coloring of the odd rim $v_0\ldots v_{\ell-1}$, impossible.

A 4-coloring is explicit: give $z$ color 3; give $a_i,b_i,c_i$ colors $0,1,2$; alternate colors 1 and 2 on $v_0,\ldots,v_{\ell-2}$ and give $v_{\ell-1}$ color 3. Therefore $\chi(G_\ell)=4$.

### Proper subgraphs are 2-degenerate

Suppose a nonempty subgraph $H\subseteq G_\ell$ has minimum degree at least three. It contains some non-$z$ vertex $u$. Since $u$ has ambient degree exactly three, all three incident ambient edges and their endpoints must lie in $H$. Applying the same argument to every newly included non-$z$ vertex and using connectivity of $G_\ell-z$ propagates to every non-$z$ vertex and all of its incident edges, including all edges to $z$. Hence $H=G_\ell$.

Thus every nonempty proper subgraph has a vertex of degree at most two. Every subgraph of a proper subgraph is still proper, so every proper subgraph is 2-degenerate and therefore 3-colorable. Hence $G_\ell$ is 4-critical.

### $K_4$-freeness

Each $v_i a_i$ is a bridge of $G_\ell-z$. A $K_4$ avoiding $z$ cannot cross such a bridge and cannot lie in either the rim cycle or an attached triangle. The neighbors of $z$ induce only the disjoint edges $b_i c_i$, so no $K_4$ contains $z$.

### Complete cycle classification

A cycle avoiding $z$ cannot use a bridge $v_i a_i$, so it is either the rim or one attached triangle; these are chordless.

A cycle through $z$ whose two neighbors of $z$ lie in one attached triangle is either $z b_i c_i z$ (zero chords) or $z b_i a_i c_i z$ (one chord).

Now let a cycle $C$ through $z$ meet two distinct attached triangles $i\ne j$ at its two neighbors of $z$. Removing $z$ leaves a simple path. Since each attached triangle has only one bridge to the rest of $G_\ell-z$, this path uses exactly the two endpoint triangles, their bridges, and one rim arc from $v_i$ to $v_j$; it cannot enter a third triangle.

Let $d$, $1\le d\le\ell-1$, be the length of that rim arc. In each endpoint triangle, the path from the chosen $b$- or $c$-vertex to $a$ has length one or two. Let $t\in\{0,1,2\}$ count the endpoints using a length-two passage. Each length-two passage contributes exactly two chords: the unused triangle edge and the unused edge from $z$ to the intermediate endpoint-triangle vertex. A length-one passage contributes none.

The rim contributes one additional chord exactly when the chosen rim arc contains all rim vertices, equivalently $d=\ell-1$; then the omitted rim edge joins the arc endpoints. Put

$$\varepsilon=\begin{cases}1,&d=\ell-1,\\0,&d<\ell-1.\end{cases}$$

No other chord can occur, so

$$\operatorname{ch}_{G_\ell}(C)=2t+\varepsilon,\qquad |V(C)|=d+t+6.$$

Therefore every cycle has at most five chords. If $C$ is odd and $\varepsilon=0$, its chord count is at most four. If $\varepsilon=1$, then $d=\ell-1$ is even, so oddness of $d+t+6$ forces $t=1$, yielding exactly three chords. Thus every odd cycle has at most four chords.

### Sharpness

For adjacent rim vertices $v_0,v_1$, use the length-two passage in both endpoint triangles. Then

$$z,b_0,c_0,a_0,v_0,v_1,a_1,c_1,b_1,z$$

is a 9-cycle with exactly four chords: $z c_0$, $z c_1$, $a_0 b_0$, and $a_1 b_1$. Replacing the rim edge $v_0v_1$ by the complementary rim arc gives an even cycle with exactly five chords, the previous four plus $v_0v_1$.

## Uniform consequence for the second question

Given any positive integer $r$, choose odd $\ell$ with $4\ell+1>r$. Every subgraph of $G_\ell$ on at most $r$ vertices is proper, hence 2-degenerate and 3-colorable, while every odd cycle of $G_\ell$ has at most four chords. Therefore no function $f(r)\to\infty$ can satisfy the proposed implication.

This is a parameter-uniform alternative disproof of the second question, not a finite-instance argument and not a full-scope proof of JSP-000907.

## Supplementary finite checks

Independent finite checks were run for odd $\ell=3,5,\ldots,19$, enumerating 19,986 simple cycles in total and confirming the chord bounds and 2-degeneracy after every single-edge deletion. For $\ell=3,5,7$, exhaustive search independently ruled out 3-colorability. These checks are supplementary only; the infinite claim follows from the proof above.

## References

1. Boris Alexeev, Moe Putterman, Mehtaab Sawhney, Mark Sellke, and Gregory Valiant, *Short proofs in combinatorics, probability and number theory II*, arXiv:2604.06609v1, Section 4: https://arxiv.org/html/2604.06609v1
2. Xiaozheng Chen and Bo Ning, *Cycle lengths and chords under chromatic and degree constraints*, arXiv:2607.15501v1: https://arxiv.org/html/2607.15501v1
3. Erdős Problem 1091 discussion: https://www.erdosproblems.com/forum/thread/1091
4. JSP-000907: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000907
