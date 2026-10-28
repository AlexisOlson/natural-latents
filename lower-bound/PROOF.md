# A lower bound C > 2 for the natural-latent constant

## Statement and standing

Use natural logarithms and nats throughout. The repository's [statement file](../NaturalLatents/Statement.lean) defines the same errors in bits; changing units multiplies both errors by the same factor. For a law $p$ of $Z=(X,Y)$, let

$$
T(p)=\min_{\Gamma=g(X,Y)}\{I(X;Y\mid\Gamma)+H(\Gamma\mid X)+H(\Gamma\mid Y)\},
$$

and let $\tau(p)$ be the infimum of $I(X;Y\mid V)+I(V;X\mid Y)+I(V;Y\mid X)$ over finite stochastic latents with marginal $p$. For the infinite-sum law defined in section 1, with the explicit latent score $\tau_L$ and the exact rational $R$ of section 7,

$$
C\geq T(p)/\tau(p)\geq T(p)/\tau_L\geq R>2.0012323023>2.
$$

This is a **paper proof with interval-certified numerical inputs and computer-checked cover evidence**, outside the Lean development. The implication uses the supplied complete 912-family cover with positive checked bounds at the specified law and price. Its historical execution-identity limitation is stated in section 8. The author reports that no human has checked these proofs line by line.

Only one law is needed. Its exact parameter is $\alpha=3502021035450561/2^{53}$. Only $\tau(p)\leq\tau_L$ is used. Neither optimality of the named latent nor the sharp value of $C$ is claimed. The two leaf-check implementations share the grid, transfer bound, bounding method and proposer search.

## 1. The law

Let $n=30$, with indices modulo $n$, and set

$$
a_j=\sum_{r\in\mathbb Z}e^{-\alpha(j+rn)^2},\quad b_j=\sum_k a_k a_{j-k},\quad m_2=b_0,\quad m_3=\sum_j a_jb_{-j},\quad\lambda_j=m_2a_j/b_j.
$$

Define the real finite Fourier transforms

$$
\rho_x=\sum_j a_j\cos(2\pi jx/n),\qquad K_d=\sum_j\lambda_j\cos(2\pi jd/n),
$$

and the component laws

$$
q_i(x,y)=\frac{K_{x-y}\rho_{x-i}^2\rho_{y-i}^2}{n^2m_2m_3},\qquad p(x,y)=\frac1n\sum_{i=0}^{n-1}q_i(x,y).
$$

Let $L$ be uniform on the component index $i$. Directed intervals verify $\rho_x>0$ and $K_d>0$, including the small value at $d=15$. **[computer-checked]** Finite Fourier convolution gives $K*\rho^2=nm_2\rho$ and $\sum_x\rho_x^3=nm_3$. Thus each $q_i$ sums to one and has marginals $\rho_{x-i}^3/(nm_3)$. This is an identity, rather than a numerical normalization test. **[paper proof]**

The mixture is circulant and even. Write $p(x,x+d)=p_d$; explicitly

$$
p_d=\frac{K_d\sum_x\rho_x^2\rho_{x+d}^2}{n^3m_2m_3}.
$$

Every cell is positive; $p_{15}\simeq4.78507217241317\cdot10^{-25}$, so $\Pr(D=15)=30p_{15}\simeq1.4\cdot10^{-23}$ ($1.4355\cdot10^{-23}$ before rounding). The decimal `0.38880243862788444` in `law.json` displays the specified binary64 value. Interpreting that decimal as an exact real parameter defines a different law with disjoint probability intervals; use the rational parameter above.

An elementary expression for this same infinite-sum law is

$$
u_d=\sum_j(a_j/b_j)\cos(2\pi jd/n),\quad v_d=\sum_jb_j^2\cos(2\pi jd/n),\quad p(x,y)=\frac{u_dv_d}{n\sum_eu_ev_e},\quad d=y-x.
$$

Indeed $K_d=m_2u_d$ and $\sum_x\rho_x^2\rho_{x+d}^2=nv_d$; also $\sum_du_dv_d=nm_3$. These identities prove equivalence. **[paper proof]** Equivalently, $X$ is uniform and $Y=X+D$, where $\Pr(D=d)=np_d$.

For an extremely close finite approximation, replace $a_j$ by $e^{-\alpha j^2}+e^{-\alpha(30-j)^2}$ in that elementary expression. An ordinary 400-digit computation in [law_elementary.py](check/law_elementary.py) finds maximum relative probability difference $1.0636\cdot10^{-133}$ and places both laws inside all stored probability intervals. Those intervals have relative widths $1.21\cdot10^{-78}$ at $d=0$, $3.0\cdot10^{-74}$ at $d=14$, $2.85\cdot10^{-74}$ at $d=16$ and $1.03\cdot10^{-59}$ at $d=15$; the last absolute width is $4.94\cdot10^{-84}$ ([doc_numbers.py](check/doc_numbers.py), `receipts/doc-numbers.log`).

Probability-box inclusion alone does not establish a stochastic score bound or exact symmetries for an arbitrary nearby law. For this particular finite coefficient vector, evenness is exact, and the same Fourier construction defines its own $q_i$. The normalization identities above hold for any even coefficient vector with the required positive transforms; they do not require an infinite Gaussian identity or any optimality property of the latent. [enclose_inputs.py](check/enclose_inputs.py) verifies positivity, all probability boxes, transfer and entropy/latent-score endpoints separately for the finite and infinite constructions. This supplies the finite-law extension; the headline continues to name the infinite-sum law unambiguously.

For cyclic distance $d\leq9$, $\Pr(D=d)=30p_d\simeq0.1641e^{-0.0846d^2}$ within 0.115 percent (the maximum relative error printed by [doc_numbers.py](check/doc_numbers.py)). The literal alias cutoff $|r|\leq20$ used during construction (the key `R` in `law.json`, unrelated to the ratio $R$) is another approximation, not exact equality with the infinite series. It is covered by the explicit tail enclosure used for the infinite law.

## 2. The upper bound on tau and positivity

The joint law $\Pr(X=x,Y=y,L=i)=q_i(x,y)/n$ is feasible for $p$, so $\tau(p)\leq\tau_L$. Expanding the three conditional mutual informations gives

$$
\tau_L=2H(Z)-2\ln n+2H(q_{0,X})+2H(q_{0,Y})-3H(q_0).
$$

For example, $I(L;X\mid Y)=H(Z)-\ln n-H(q_0)+H(q_{0,Y})$; the other terms give the displayed sum. **[paper proof]** Directed interval arithmetic gives $\tau_L=0.43152285591856168283\ldots$ nats, or $0.62255588426395\ldots$ bits, below the stored `tau_up`. The independent 115-digit computation encloses it with width below $4\cdot10^{-112}$; this is the recomputation's width, not the width of the stored interval. **[computer-checked]**

The ratios also require $\tau(p)>0$. A finite stochastic latent is a mixture of conditional laws of $Z$. Its score is a fixed term depending on $p$ plus the mixture average of the continuous function $2H(q_X)+2H(q_Y)-3H(q)$. Caratheodory's theorem reduces the mixture to at most $|Z|+1$ components while preserving $p$ and that average. Compactness therefore gives an attaining latent. If its score were zero, all three nonnegative conditional mutual informations would vanish. The last two imply $\Pr(V=v\mid x,y)=\Pr(V=v\mid x)=\Pr(V=v\mid y)$ on the full support, hence $V$ is independent of $Z$. The first then forces $I(X;Y)=0$. But $p$ has uniform marginals and unequal cell probabilities, so it is not a product. This contradiction proves positivity, without asserting that $L$ is optimal. **[paper proof]**

## 3. True-law symmetries

Let $G$ be generated by $(x,y)\mapsto(x+a,y+a)$ and $(x,y)\mapsto(y,x)$. Uniform translate averaging gives the first invariance. The coefficients are even, hence $K$ is even and $q_i(x,y)=q_i(y,x)$, giving the second. For a block, diagonal translations permute its row and column masses; transposition exchanges them. Thus the block cost, total mass, and a price depending only on cyclic distance are invariant. Translate averaging alone would not imply transposition invariance. **[paper proof]**

## 4. Grid, transfer and zero cells

The checks use $P(x,y)=\texttt{p\_int}[y-x]/2^{52}$. Its total is $(2^{52}-46)/2^{52}$ and is not renormalized. With $h(t)=-t\ln t$, $h(0)=0$, write the cost of a block as

$$
c(U)=2\sum_i h(r_i)+2\sum_jh(c_j)-h(m).
$$

The supplied transfer constant is

$$
\Delta=\frac{39513286862838429351448961700400615940267}{766247770432944429179173513575154591809369561091801088}\simeq5.157\cdot10^{-14}.
$$

It bounds the sum of maximum endpoint errors between the certified probabilities and the grid over all 900 cells. Directed re-enclosure leaves more than $3.3\cdot10^{-55}$ below this bound. **[computer-checked]**

For $0\leq x,y\leq1$ and $|x-y|\leq1/2$, concavity gives $|h(x)-h(y)|\leq h(|x-y|)$: the extremal increment magnitudes are $h(d)$ and $h(1-d)$, and $h(1-d)\leq h(d)$ for $d\leq1/2$. In a fixed block, the absolute row errors sum to at most $\Delta$, as do the column errors; its total-mass error is at most $\Delta$. Jensen and monotonicity of $h$ on the error range, using $\Delta<1/4$, give

$$
|c_{\rm true}(U)-c_{\rm grid}(U)|\leq E_{\rm block}=4n h(\Delta/n)+h(\Delta).
$$

Both true and grid block masses lie in $[0,1]$. **[paper proof]** The stored `error` in `transfer.json`, about $8.5903\cdot10^{-12}$, exceeds this expression by more than $3\cdot10^{-74}$ under directed arithmetic. The separate checker also checks this inequality with its own 400-bit logarithms. **[computer-checked]**

If a true block mass belongs to $(lo_j/960,hi_j/960]$, its grid mass belongs to the closed interval widened by $\Delta$. Every such window is retained, with edges rounded outward to grid integers. At a shared edge both penalties are tested; the larger penalty gives the smaller residual bound. The penalty remains the one at the true mass when cost is transferred. **[paper proof]**

Only the distance-15 cells have zero grid mass; their true probabilities are positive and their price $\gamma_{15}$ is nonpositive, about $-2.396\cdot10^{-6}$. Removing a free such cell $z$ changes no grid masses and changes the residual by $+\gamma_z\leq0$. Consequently a lower bound for the reduced block also bounds the original. Logical propagation uses the actual on/off assignments, including any forced zero-grid cells, before free zero-grid cells are omitted from bounding. Artificial off assignments introduced by this omission are never used in propagation. The transfer error is charged to the entire original block, including its positive true distance-15 mass. **[paper proof]**

## 5. Fibre identity, dual and root coverage

For a deterministic $\Gamma=g(Z)$, expand the entropies to obtain

$$
D(\Gamma)=2H(X,\Gamma)+2H(Y,\Gamma)-H(\Gamma)-H(Z)-H(X)-H(Y).
$$

The probabilities of $(X,\Gamma)$ and $(Y,\Gamma)$ on a fibre $A$ are its unnormalized row and column masses; the probability of that label is $m(A)$. Therefore

$$
D(\Gamma)=\sum_{A\text{ fibre of }\Gamma}c(A)-H(Z)-H(X)-H(Y).\tag{F}
$$

This is elementary entropy algebra, not a new identity. Every partition of the 900 cells is represented by a deterministic code with at most 900 used labels; empty labels contribute zero. Taking its minimum gives the repository's $T(p)$. **[paper proof]**

Let $\gamma_z$ be a cell price and let $\phi$ be constant on the 481 windows $(lo_j/960,hi_j/960]$, with $\phi_0=0$ and $\phi\leq0$. Define $\Phi_0=\inf\sum_i\phi(m_i)$ over finite multisets of positive masses summing to one. Suppose

$$
c_{\rm true}(U)\geq\sum_{z\in U}\gamma_z+\phi(m_{\rm true}(U))\quad\text{for every nonempty }U.\tag{B}
$$

All true cells are positive. Each nonempty fibre has positive mass, the masses sum to one, and the fibres partition all cells. Sum (B), use (F), then minimize over partitions to get

$$
T(p)\geq\mathrm{Sum}_{\gamma}+\Phi_0-H(Z)-H(X)-H(Y).\tag{D}
$$

No restriction to rectangles or symmetric partitions is imposed. **[paper proof]**

With $\phi\equiv0$, (B) and (D) are the price dual used in Satya Benson's published lower bound: `DualValid` and `T_lower_of_dual` in `StochToDet1960/Bound.lean` of [satchlj/stoch-to-det-lower](https://github.com/satchlj/stoch-to-det-lower), as read at its commit `15ae7dae` (a declaration of the same name is in `StochToDet1948/Bound.lean` there). The block-mass penalty $\phi$ with its exact packing minimum, the cover by symmetry roots that makes the subset condition checkable at $n=30$, and the law are specific to this proof.

It remains to cover all nonempty subsets up to $G$. Let $d$ be the least cyclic distance in $U$, transpose if needed so it meets $L_d=\{(t,t+d)\}$, and put $T=\{t:(t,t+d)\in U\}$. All cells of distance below $d$ are off. After a diagonal translation, one of three cases applies:

1. $T$ is the whole line: root `d_ALL`.
2. $T$ is proper with longest run $L\geq2$: cells $0,\ldots,L-1$ are on, $L$ and 29 are off, and no $L+1$ consecutive line cells are all on. This is root `d_L{L}`.
3. Every run has length one: choose a member followed by a longest gap $G$, and translate that member to 0. Cells $1,\ldots,G$ and 29 are off. If $G\leq27$, cell $G+1$ is on. Gap 28 is impossible because it would make cell 29 on beside cell 0. Gap 29 is the singleton case, with no additional on-cell. Impose runs at most one and gaps at most $G$: root `d_L1_G{G}`.

Ties require any maximizing choice. Families may overlap. There are $16(1+28+28)=912$ roots; the construction is implemented separately in the two checkers. This covers every nonempty subset. **[paper proof]** Historical exhaustive checks at $n=4$ and $n=5$ found zero uncovered blocks among 65,535 and 33,554,431 nonempty blocks, respectively; the two root lists were also compared at $n=4,5,6,30$. Those are finite checks supporting the implementation, not an exhaustive $n=30$ subset test.

A family leaf is reached by a recorded binary path. Rebuilding the root and applying sound unit propagation gives forced-on, forced-off and free cells. Duplicate leaves, repeated cells on a path, inconsistent branch variables, internal leaves or missing children are rejected by the separate checker's prefix test. Kraft sum one is checked exactly. Every family assignment then follows a path to one leaf; every block in that family lies in its rebuilt node. The supplied cover has 912 families, 6,897,062 nodes and 3,448,987 stored leaves. **[computer-checked cover evidence]**

## 6. Leaf bounds

After omitting only free zero-grid cells, let $A$ be forced on and $W$ range over the remaining free cells. Set $F(V)=2\sum h(r_i)+2\sum h(c_j)$ and $S(W)=F(A\cup W)-F(A)-\gamma(W)$. Concavity of $h$ and nonnegative modular masses make $F$, and hence $S$, submodular. For any free-cell ordering, its greedy vector $v$ satisfies $v(W)\leq S(W)$: each increment along the subset is at least the corresponding increment along the larger greedy prefix. Convex combinations remain minorants. **[paper proof]**

The certificate supplies permutations and nonnegative integer weights summing to $2^{40}$. The checker validates them and computes componentwise lower bounds using outward entropy intervals. At fixed free mass, allowing indicators in $[0,1]$ gives a lower bound by fractional knapsack. Sorting is exact: the key is $\lfloor x_e2^{107}/p_e\rfloor$ with integer coefficients and grid masses $p_e<2^{52}$, so distinct ratios cannot collide out of order. On each knapsack segment and each widened window use

$$
M\ln M\geq(1+\ln q)M-q\qquad(q>0,\ M\geq0).
$$

Any positive dyadic proposal for $q$ is valid; its logarithm is re-enclosed. The remaining affine function is minimized at an endpoint. Empty free sets and $M=0$ are handled directly. Subtract the stored transfer error from the resulting grid bound. A nonvacuous node is accepted exactly when that final rational lower bound is positive; a logically empty node is accepted after independent reconstruction. The checker rebuilds the path and rejects disagreement with the claimed forced-on or nonzero free set. **[computer-checked]**, based on the paper inequalities above.

## 7. Packing and the exact scalar

The packing minimum concerns real masses, not just integer multiples of $1/960$. Because $\phi_0=0$, any positive leftover mass can be filled with finitely many masses in $(0,1/960]$ at zero cost. Counts $c_j$ of positive-index windows are therefore feasible exactly when $\sum_{j>0}c_jlo_j<960$: necessity follows from the strict lower edges; sufficiency follows by adding sufficiently small positive increments above them and filling the remainder in window 0. Thus an unbounded integer knapsack on lower-edge budget 959 computes the same infimum without discretizing the real masses. This also explains the strictness condition in the two supplied dynamic programs. **[paper proof]**

The exact value is $\Phi_0=-27811237776763/281474976710656$, attained by windows 146, 146, 144 and 45: masses $583/2,583/2,575/2,179/2$ in units of $1/960$ sum to 960 and lie in their respective windows. A non-strict lower-edge budget would wrongly admit windows 111, 121, 123 and 127 at lower cost. **[computer-checked arithmetic]**

The cell-price sum is $\mathrm{Sum}_{\gamma}=1896178602705315/140737488355328$. The numerical input checks establish $H(Z)\leq\texttt{HXY\_up}$, $H(X)\leq\texttt{HX\_up}$, $H(Y)\leq\texttt{HY\_up}$ and $\tau_L\leq\texttt{tau\_up}$. In exact rational arithmetic,

$$
N=\mathrm{Sum}_{\gamma}+\Phi_0-\texttt{HXY\_up}-\texttt{HX\_up}-\texttt{HY\_up}>0,
$$

with $N=0.863577478472262\ldots$ nats, or $1.24587894561533\ldots$ bits (both as printed by [doc_numbers.py](check/doc_numbers.py)). Equation (D) gives $T(p)\geq N$. Positivity from section 2 and $\tau(p)\leq\tau_L\leq\texttt{tau\_up}$ give

$$
T(p)/\tau(p)\geq T(p)/\tau_L\geq N/\texttt{tau\_up}=R.
$$

Here

$$
R=\frac{102395331021410935836841843679114580027925957092193752396069619230740137245107404}{51166139433434760740393189165888283730804952847474027374683157095605028939972369}.
$$

It is exactly the `conditional_ratio_lower` field of `price_v4.json`; its decimal begins $2.001232302363234632108688941311\ldots$ (truncated). The comparison $R>2.0012323023$ is exact. **[computer-checked]** For every admissible universal constant, $T(p)\leq C\tau(p)$ forces $C\geq R$; taking the infimum preserves this inequality. No attainment of the sharp constant is assumed. **[paper proof]**

The separate scalar script is a reporting calculator: its equality flags do not themselves cause failure. The wrapper checks those flags, exact agreement between both scalar implementations and the stored value, and the strict rational threshold. Scalar agreement alone does not establish identity or feasibility of all inputs.

### How tight is the bound for this law

Every deterministic code $\Gamma=g(X,Y)$ has cost $D(\Gamma)\geq T(p)$, so one explicit code gives an upper bound on $T(p)$. Take $\Gamma=G(X)$, grouping $X\in\mathbb Z_{30}$ into four consecutive blocks of sizes $8,8,7,7$. Because $G$ is a function of $X$, $H(G\mid X)=0$ and $I(X;Y\mid G)=H(X)+H(Y,G)-H(G)-H(X,Y)$; also $H(G\mid Y)=H(G,Y)-H(Y)$. Since $X$ and $Y$ are uniform, $H(X)=H(Y)=\ln 30$, and $H(X,Y)=\ln 30+H(q)$ for $q_d=30p_d$ (because $Y=X+D$ with $D$ independent of $X$). Hence

$$
D(G)=2H(G,Y)-H(G)-H(q)-\ln 30 .
$$

The law is circulant, so a rotation of $X$ and $Y$ together leaves it unchanged; the cost of a consecutive-block code therefore depends only on the block sizes in cyclic order, not on where the first block starts.

[code_upper.py](check/code_upper.py) evaluates $D(G)$ in mpmath interval arithmetic over the enclosures $pd\_lo/pd\_up$ of `data/law.json` (log in `receipts/code-upper.log`). It certifies $D(G)=0.867043489500587034\ldots$ nats $=1.25087934253755892\ldots$ bits, hence $T(p)\leq 1.2508793426$ bits, and with the stored $\tau_L$ enclosure

$$
2.0012323023<\frac{T(p)}{\tau_L}\leq 2.0092643475 .
$$

**[computer-checked]**, interval arithmetic. The float64 search that chose the blocks is not part of the claim; any code gives a valid upper bound. This bounds $T/\tau_L$, not $T/\tau$: $\tau(p)$ could be below $\tau_L$, which would only raise $T/\tau$. It is therefore not an upper bound on $C$ and not a claim about the sharp constant.

## 8. Arithmetic, executions and limits

The separate checker uses outward integers at scale $2^{-96}$ and exact rational comparisons. JSON prices are interpreted as exact binary64 rationals. Floating-point calculations propose orders and tangent points but do not replace enclosures. Logarithms use an atanh-series table plus an alternating series, rounded outward. In the relevant integer range up to $2^{200}$, a safe bracket-width statement is below $2^{-65}$; rounding can make the full bracket slightly wider than $2^{-66}$. Historical tests enclosed 19,933 random logarithm arguments and 5,000 grid entropies against 60-digit mpmath. These tests support the implementation; they do not replace the series remainder bounds.

Input enclosures were independently recomputed at 110 and 115 digits. The public numerical checker [enclose_inputs.py](check/enclose_inputs.py) verifies the endpoints directly, including positivity and the transfer constants. The 400-digit elementary comparison alone is not an interval certificate. The stored upper-end margins are about $5.35\cdot10^{-78}$ for $H(Z)$, $3.40\cdot10^{-78}$ for each marginal entropy and $5.03\cdot10^{-77}$ for $\tau_L$.

The original assembler, now `check/refreeze/rf/final.py`, checks all family summaries, price hashes, stored minima and leaf counts; it re-reads and prefix-checks their leaf sets, compares window specifications and recomputes the packing value and ratio. It does not recompute leaf bounds. Original family generation checked them inline. The separate historical replay certified all 3,448,987 stored leaves, five after splitting, with none uncertified. The assembler's minimum was about $1.0034\cdot10^{-7}$. This reflects the proposer's $10^{-7}$ stopping target; it is not a measure of mathematical slack or optimality.

A separate model-run validation regenerated 11 replay jobs (42,145 leaves, about 1.6 percent of the leaves of the 15 families added in the final revision of the cover) byte for byte; it supported the cover evidence and did not examine the analytic chain. Two further model readers checked the analytic steps (transfer, zero-cell omission, symmetry, duality, the fibre identity, the entropy and latent-score inputs, and the final division), and one also checked root coverage. These are model readings, not human checks.

The two leaf-check implementations have separate code and arithmetic but share $\Delta$, the grid, the mathematical method and the proposer. Those shared premises require the paper arguments and input-enclosure checks, not agreement between implementations alone.

Historical full-replay receipts hash decompressed leaf or proposal content but do not bind the law, price, transfer or checker for every execution. Frozen manifests and final input hashes support agreement of unsampled historical inputs with the supplied files; this remains an inference. The newer subset logs identify current packaged inputs but do not authenticate all earlier executions. The wrapper re-hashes the packaged files against `MANIFEST.sha256`; it does not read or authenticate receipts. The elementary-law receipt lacks script and input hashes.

Full and quick wrapper modes both omit leaf-bound recomputation; quick also omits prefix coverage. Per-leaf mode is the separate bound replay, with prefix coverage only for complete selected families. None of these modes by itself recomputes the input enclosures. The upper bound in section 7 concerns $T/\tau_L$. No upper bound on $T/\tau$ or $C$, equality $\tau=\tau_L$, exact value of $T/\tau$ or sharp value of $C$ is asserted.
