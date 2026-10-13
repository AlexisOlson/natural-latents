# The setup on a connected support

This page proves that every finite law $`p`$ whose support is connected has a setup latent: a finite latent $`L`$ that
attains $`\tau(p)`$, with positive priors and pairwise distinct components, all of which are contacts of one common
feasible kernel, are positive on the whole support, and give positive posterior rows there. The proof has three steps:
an optimal latent and an affine minorant of the component functional $`\phi`$ (Lemma S1.2), a normalization that turns
the minorant into one feasible kernel whose contacts are exactly the components with zero gap (Lemma S1.3), and the
propagation of positivity along the connected support (Lemma S1.4); Lemma S1.1 is the cost identity they rest on. The
assembly `NaturalLatents.General.T_le_of_connected` (`NaturalLatents/General/Pricing.lean`) starts by obtaining this
setup from `exists_setup_of_connected`. It applies the race to the setup latent and its positive posterior rows, forms
each pair of distinct components as two positive contacts of the common kernel for the [contact moments](contact.md)
and the [affinity bound](affinity.md), passes the whole setup to the mismatch payment, and uses $`M+B=\tau(p)`$ in its
last step, as steps 1 to 8 of the [route](overview.md#the-route) describe.

Each lemma below states its hypotheses, so that it can be read alone. Unless prefixed `stoch_to_det`, the Lean
declarations named below are in the namespace `NaturalLatents.General`; the `stoch_to_det` declarations are in
`NaturalLatents/Upstream/`, adapted from [DLorell/stoch_to_det](https://github.com/DLorell/stoch_to_det) (see the
[upstream inputs](upstream.md)). The analytic content of Lemmas S1.2 to S1.4 is proved in Lean by that upstream code;
only the final assembly is in `NaturalLatents/General/Setup.lean`. The exceptions to the naming rule are the
declarations called private below (`Valid`, `exists_approx_valid_certificate`, `exists_optimal_valid_certificate`,
`exists_tau_optimal_kernel`, `valid_iff_feasible`, `maximizer_rpow_two_thirds`, `Gdef_eq_certificate_gap` and
`Gdef_eq_zero_iff`): they are Lean-private declarations in the namespace `stoch_to_det`, in the public file
`NaturalLatents/Upstream/Duality.lean`.

## 1. The setup on a connected support

> **Setup, connected support.** Given a law $`p`$ whose support $`S`$ is connected (as a bipartite row-column graph),
> there is an attained latent $`L`$ with $`M+B=\tau(p)`$, priors $`\pi_i>0`$, distinct components (duplicates merged),
> each a contact of one common feasible kernel $`w>0`$ on $`S`$ and positive on $`S`$, and posterior rows positive on
> $`S`$.

The proof is a supporting-plane argument and a normalization argument, with the support made explicit. Attainment and
the affine minorant hold for every finite law; connectedness is needed only to make all contacts positive.

Units and conventions are those of section 0 of the [contact page](contact.md): entropies, mutual informations and
relative entropies are in nats, conditional sums range over positive-probability conditioning events, and
$`0\ln0=0`$. The entropy $`H(q)`$ and the relative entropy $`D(a\Vert b)`$, for probability laws $`a,b`$ with
$`\mathrm{supp}\,a\subseteq\mathrm{supp}\,b`$, are as in (D2). All alphabets are finite and nonempty; $`X,Y`$ denote
both the coordinates and their alphabets, and $`Z=(X,Y)`$. For a probability law $`p`$ on $`X\times Y`$ and any
probability law $`q`$ on $`X\times Y`$, with marginals $`q_X,q_Y`$, set

```math
\phi(q)=2H(q_X)+2H(q_Y)-3H(q),\qquad
c(p)=2H(p)-H(p_X)-H(p_Y).
\qquad \text{(S1.A)}
```

A finite latent $`L`$ of $`p`$, its budgets $`M_L=I(X;Y\mid L)`$ and $`B_L=I(L;X\mid Y)+I(L;Y\mid X)`$, and the
stochastic optimum $`\tau(p)=\inf_L(M_L+B_L)`$ are as in (D3); concretely, a finite latent is a finite nonempty label set $`I`$, probability weights
$`(\pi_i)_{i\in I}`$ and probability laws $`(q_i)_{i\in I}`$ on $`X\times Y`$ with $`p=\sum_i\pi_iq_i`$ and
$`\mathbb P(L=i,Z=z)=\pi_iq_i(z)`$. Zero priors are allowed here; their component laws may be chosen arbitrarily.

Lean: a finite latent is `stoch_to_det.Latent` (`NaturalLatents/Upstream/Functionals.lean`); `mediation`,
`redundancy`, `negPhiNat` and `psiNat` are in `NaturalLatents/General/Definitions.lean`. `negPhiNat q` is
`-(nats (stoch_to_det.Phi q))` and `psiNat p` is `nats (stoch_to_det.Psi p)`, with `nats` the multiplication by
`Real.log 2` of `NaturalLatents/General/Nats.lean`, where the bit-valued
`stoch_to_det.Phi` $`=3H(q)-2H(q_X)-2H(q_Y)`$ and `stoch_to_det.Psi` are in `NaturalLatents/Upstream/Entropy.lean`;
the page's $`\phi`$ is therefore minus upstream's `Phi`, converted to nats.

Some letters on this page are local: $`a,b`$ in $`D(a\Vert b)`$ and (S1.P) are probability laws, not the race exponent
$`a`$ or the quadratic $`b`$ of (A2.1); $`u,v`$ are probability laws on $`X`$ and $`Y`$, not the price bound $`u`$;
$`c(p)`$ is the constant term of (S1.A), not the constant of the theorem; $`R(p)`$ is the value (S1.H), not a contact;
the $`d`$ of Carathéodory's theorem is a dimension, not the mismatch; $`E`$ is the set (S1.K) and $`\lambda`$ a
coefficient in (S1.L); and $`\Phi`$, $`\Psi`$ in the Lean notes are upstream's bit-valued `Phi` and `Psi`, not the
separation price $`\Psi`$ of (A2.1).

Write $`S=\{z:p(z)>0\}`$. This set is nonempty. Its active row and column alphabets are
$`X_S=\{x:\exists y,(x,y)\in S\}`$ and $`Y_S=\{y:\exists x,(x,y)\in S\}`$. Connectedness means that the bipartite graph
with vertices $`X_S\sqcup Y_S`$ and edges $`S`$ is connected; equivalently, the cells of $`S`$ are connected by
shared-row and shared-column steps. Unused rows and columns do not create vertices in this graph. We keep the original
alphabets in the formulas, so all laws on an active alphabet are extended by zero on unused coordinates.

Lean: the support is `stoch_to_det.support`, and `stoch_to_det.IsConnected`
(`NaturalLatents/Upstream/Functionals.lean`) asks that any two cells of $`S`$ be joined by a chain of cells of $`S`$,
each sharing a row or a column with the next (`stoch_to_det.Adj`); this is the cell form of the definition above.

For a kernel $`w`$ that is positive on $`S`$ and zero outside $`S`$, and for probability laws $`u`$ on $`X`$ and $`v`$
on $`Y`$, write

```math
\Lambda(w;u,v):=\sum_{(x,y)\in S}w(x,y)u(x)^{2\text/3}v(y)^{2\text/3}.
\qquad \text{(S1.B)}
```

Feasibility and contact are defined in (C1.1) and (C1.2) on the
[contact page](contact.md#1-contact-moments-and-the-feasible-hessian): $`w`$ is feasible when $`\Lambda(w;u,v)\le1`$
for every such $`u,v`$, and a contact of $`w`$ is a probability law supported on $`S`$ that satisfies the contact
equation (C1.2) on $`S`$. The contact equation then also holds off $`S`$, where both sides vanish. On this page both are
read on the original alphabets: feasibility for all $`u,v`$ on $`X`$ and $`Y`$ implies the required feasibility on the
active alphabets, and allowing unused coordinates in $`u,v`$ does not impose any positivity requirement on them. Unlike
the positive contacts of the contact page, defined after unused rows and columns are removed, a contact here keeps the
original alphabets and is not assumed positive on $`S`$; Lemma S1.4 proves that positivity.

Lean: $`\Lambda`$ is `stoch_to_det.Lambda`, feasibility is `stoch_to_det.Feasible`, which also records $`w>0`$ on
$`S`$, and the contact property is `stoch_to_det.IsContact` (a probability law, zero off $`S`$, satisfying the contact
equation on $`S`$), all in `NaturalLatents/Upstream/Duality.lean`. Neither constrains $`w`$ outside $`S`$.

**Lemma S1.1 (universal finite entropy cost identity).** For every finite nonempty $`X,Y`$, every probability law $`p`$
on $`X\times Y`$, and every finite latent $`L`$ of $`p`$, including zero priors,

```math
M_L+B_L=c(p)+\sum_{i\in I}\pi_i\phi(q_i).
\qquad \text{(S1.C)}
```

*Proof.* Write $`q_{iX}`$ and $`q_{iY}`$ for the two marginals of $`q_i`$. Conditional entropy is the weighted
entropy of the conditional law, so

```math
\begin{aligned}
H(X\mid L)&=\sum_i\pi_iH(q_{iX}),&
H(Y\mid L)&=\sum_i\pi_iH(q_{iY}),&
H(Z\mid L)&=\sum_i\pi_iH(q_i),\\
H(X\mid Y)&=H(p)-H(p_Y),&
H(Y\mid X)&=H(p)-H(p_X),\\
H(X\mid Y,L)&=\sum_i\pi_i\bigl[H(q_i)-H(q_{iY})\bigr],&
H(Y\mid X,L)&=\sum_i\pi_i\bigl[H(q_i)-H(q_{iX})\bigr].
\end{aligned}
\qquad \text{(S1.D)}
```

Expanding each of the three mutual information terms gives

```math
\begin{aligned}
M_L
 &=\sum_i\pi_i\bigl[H(q_{iX})+H(q_{iY})-H(q_i)\bigr],\\
I(L;X\mid Y)
 &=H(p)-H(p_Y)-\sum_i\pi_iH(q_i)+\sum_i\pi_iH(q_{iY}),\\
I(L;Y\mid X)
 &=H(p)-H(p_X)-\sum_i\pi_iH(q_i)+\sum_i\pi_iH(q_{iX}),\\
M_L+B_L
 &=2H(p)-H(p_X)-H(p_Y)
   +\sum_i\pi_i\bigl[2H(q_{iX})+2H(q_{iY})-3H(q_i)\bigr].
\end{aligned}
\qquad \text{(S1.E)}
```

This is (S1.C). No support, connectedness, positivity or optimality assumption was used. The term $`c(p)`$ remains in
the additive cost. $`\square`$

Lean: `score_nats` (`NaturalLatents/General/Definitions.lean`), with `mediation_add_redundancy_eq_score` identifying
`mediation L + redundancy L` with `nats L.score`; it converts the bit-valued identity `stoch_to_det.Latent.score_eq`
(`NaturalLatents/Upstream/Envelope.lean`), score $`=\Psi(p)-\sum_i\pi_i\Phi(q_i)`$, by `nats`, rather than expanding
the entropies as above.

**Lemma S1.2 (attainment and a finite affine minorant).** For every finite nonempty $`X,Y`$ and every probability law
$`p`$ on $`X\times Y`$, there are a finite latent decomposition of $`p`$, positive priors $`\pi_i`$, pairwise distinct
component laws $`q_i`$ supported on $`S=\mathrm{supp}\,p`$, and a real vector $`\ell`$ on the whole rectangle, such
that $`M_L+B_L=\tau(p)`$, $`\ell=0`$ off $`S`$, and

```math
\phi(q)\ge\ell\cdot q\quad(q\in\Delta_S),\qquad
\ell\cdot p=R(p),\qquad
\phi(q_i)=\ell\cdot q_i\quad(i\in I).
\qquad \text{(S1.F)}
```

Here $`\Delta_S`$ denotes the probability simplex on $`S`$, embedded by zero extension,
$`\ell\cdot q=\sum_{z\in S}\ell_zq(z)`$ on that simplex, and $`R(p)`$ is the infimum (S1.H) of the average of $`\phi`$
over finite mixtures in $`\Delta_S`$ with barycenter $`p`$, attained in the proof below. The minorant in (S1.F) is asserted only on $`\Delta_S`$. No connectedness is assumed.

*Proof.* If $`\pi_i>0`$ in any decomposition of $`p`$, nonnegativity gives

```math
0\le\pi_iq_i(z)\le p(z),\qquad
p(z)=0\ \Longrightarrow\ q_i(z)=0.
\qquad \text{(S1.G)}
```

Thus zero-prior terms may be deleted and every remaining component belongs to $`\Delta_S`$. Set
$`n=\lvert S\rvert\ge1`$. The continuous extension of $`t\ln t`$ at zero makes $`\phi`$ continuous on $`\Delta_S`$.
Its graph is compact:

```math
G=\{(q,\phi(q)):q\in\Delta_S\},\qquad
R(p)=\inf\left\{\sum_j\alpha_j\phi(Q_j):
\alpha_j\ge0,\ \sum_j\alpha_j=1,\ Q_j\in\Delta_S,\ \sum_j\alpha_jQ_j=p\right\}.
\qquad \text{(S1.H)}
```

Carathéodory's theorem says that a point in a convex hull in affine dimension at most $`d`$ is a mixture of at most
$`d+1`$ points. The graph's ambient affine space has dimension $`(n-1)+1=n`$. Every finite mixture value in (S1.H)
therefore has a representation using at most $`n+1`$ graph points. The space of those bounded-label mixtures with
barycenter $`p`$ is a nonempty closed subset of a product of compact simplices, and hence is compact. The continuous
average $`\phi`$ attains its minimum there. Lemma S1.1 consequently gives

```math
\tau(p)=c(p)+R(p)=c(p)+\sum_j\alpha_j\phi(Q_j).
\qquad \text{(S1.I)}
```

Delete zero weights. For each class $`k`$ of identical component laws, let $`Q'_k`$ be that law and sum the priors in
the class. This makes the component laws distinct while preserving the mixture and cost:

```math
\pi'_k=\sum_{j:Q_j=Q'_k}\alpha_j>0,\qquad
\sum_k\pi'_kQ'_k=p,\qquad
\sum_k\pi'_k\phi(Q'_k)=\sum_j\alpha_j\phi(Q_j).
\qquad \text{(S1.J)}
```

Relabel this merged optimum $`(\pi_i,q_i)_{i\in I}`$.

To obtain the minorant, Carathéodory also makes $`\mathrm{conv}\,G`$ compact: it is the image of a compact weight
simplex times $`G^{n+1}`$. Thus

```math
E=\mathrm{conv}\,G+\bigl(\{0\}\times[0,\infty)\bigr)
\qquad \text{(S1.K)}
```

is closed and convex. For closedness, a convergent sequence in this sum has a subsequence whose compact first summand
converges; the remaining summands then converge in the closed vertical ray. The point $`(p,R(p))`$ belongs to $`E`$, being
the mixture of graph points given by the attaining mixture (S1.I), and it is on the boundary of $`E`$, since all points $`(p,t)`$ with $`t<R(p)`$ are outside $`E`$.

The finite-dimensional supporting-hyperplane theorem states that a boundary point of a closed convex set has a nonzero
supporting linear functional. Apply it in the affine space
$`\{q\in\mathbb R^S:\sum_{z\in S}q_z=1\}\times\mathbb R`$, using the tangent space
$`V=\{v\in\mathbb R^S:\sum_{z\in S}v_z=0\}`$. Thus these directions are confined to the support face. With the
orientation chosen toward $`E`$, the functional has the form

```math
a_0\cdot(q-p)+\lambda\bigl(t-R(p)\bigr)\ge0
\quad((q,t)\in E),\qquad
(a_0,\lambda)\ne0\text{ on }V\times\mathbb R.
\qquad \text{(S1.L)}
```

Upward closure gives $`\lambda\ge0`$. If $`\lambda=0`$, then for each $`v\in V`$, positivity of $`p`$ on $`S`$
permits both $`p+\varepsilon v`$ and $`p-\varepsilon v`$ in $`\Delta_S`$ for sufficiently small $`\varepsilon>0`$.
Evaluating (S1.L) at their graph points forces $`a_0\cdot v=0`$ for every $`v\in V`$. The functional would be zero, a
contradiction. Hence $`\lambda>0`$. Put $`\eta=a_0\text/\lambda`$ and explicitly extend the affine coefficients to the
whole rectangle, with the two cases on and off the support:

```math
\ell_z=
\begin{cases}
R(p)+\eta\cdot p-\eta_z,&z\in S,\\
0,&z\notin S.
\end{cases}
\qquad
\ell\cdot q=R(p)+\eta\cdot p-\eta\cdot q
\quad(q\in\Delta_S).
\qquad \text{(S1.M)}
```

Use $`(q,\phi(q))\in E`$ in the normalized supporting inequality. It gives $`\phi(q)\ge\ell\cdot q`$ on
$`\Delta_S`$, and substituting $`q=p`$ gives $`\ell\cdot p=R(p)`$. The component gaps are nonnegative and have
weighted sum zero:

```math
\sum_i\pi_i\bigl[\phi(q_i)-\ell\cdot q_i\bigr]
=R(p)-\ell\cdot\sum_i\pi_iq_i
=R(p)-\ell\cdot p=0.
\qquad \text{(S1.N)}
```

Every $`\pi_i`$ is positive, so each gap is zero. This proves (S1.F). The classical facts used are Carathéodory and the
finite-dimensional supporting-hyperplane theorem, in the forms stated above; see Rockafellar, *Convex Analysis*,
Theorem 17.1 and Corollary 11.6.1. $`\square`$

Lean: attainment is `stoch_to_det.exists_tau_optimal_latent` and (S1.I) is `stoch_to_det.tau_eq_Psi_sub_envelope`, with
$`R(p)`$ equal to $`-\ln2`$ times `stoch_to_det.concaveEnvelopePhi` (all in `NaturalLatents/Upstream/Envelope.lean`);
the minorant is built inside `stoch_to_det.exists_common_contact_pair` (`NaturalLatents/Upstream/Duality.lean`),
through the private `exists_tau_optimal_kernel`. There it is a bit-valued certificate $`\kappa=-\ell\text/\ln2`$
(the variable `c` in `Duality.lean`), and the minorant property is the private predicate `Valid`:
$`\Phi(q)\le\sum_{z\in S}\kappa_zq(z)`$, with $`\Phi`$ upstream's bit-valued `Phi`, for every probability law $`q`$ supported on $`S`$. An exact certificate is
obtained by the private `exists_approx_valid_certificate` and `exists_optimal_valid_certificate`. The Lean differs
from the page in five ways:

- **Attainment.** `exists_tau_optimal_latent` maximizes $`\sum_i\pi_i\Phi(q_i)`$ over the compact slice at $`p`$ of the
  convex hull of the graph of `Phi` over all laws on $`X\times Y`$, and reads a latent off the maximizer; it records no
  bound on the number of labels.
- **Minorant.** Instead of a supporting hyperplane at the boundary point, the Lean strictly separates the point
  $`\varepsilon`$ beyond the optimal value over $`p`$ from the compact convex hull of the graph of `Phi` over the laws
  supported on $`S`$ (Mathlib's `geometric_hahn_banach_closed_point`), which makes the vertical coefficient positive
  without the perturbation $`p\pm\varepsilon v`$, and then takes an exact certificate as a minimizer of the value at
  $`p`$ over the compact set of valid certificates that vanish off $`S`$, are nonnegative on $`S`$ (since
  $`\phi(\delta_z)=0`$ for the point mass $`\delta_z`$) and have value at $`p`$ at most the optimum plus one.
- **Positive priors.** Zero-prior labels are pruned by `stoch_to_det.exists_seedSetup`
  (`NaturalLatents/Upstream/Seed.lean`), after the contact step. In Lean the pruning, and the merging below, are done
  only for connected support (`exists_seedSetup` takes the connectedness hypothesis, and `exists_clustering` takes a
  `stoch_to_det.SeedSetup`); the unconditional Lean statement is `exists_common_contact_pair`, whose zero-prior
  components may be arbitrary.
- **Distinct components.** Duplicates are merged only at the end, by `stoch_to_det.exists_clustering`
  (`NaturalLatents/Upstream/Quotient.lean`) inside `exists_setup_of_connected` (`NaturalLatents/General/Setup.lean`),
  and not before the minorant as in (S1.J).
- **The equality case.** The zero gaps (S1.N) are proved for an arbitrary optimal latent given by
  `exists_tau_optimal_latent`, not for the latent built in the proof.

**Lemma S1.3 (normalization gives one feasible kernel and its contacts).** For every finite nonempty $`X,Y`$, every
probability law $`p`$ on $`X\times Y`$, and every vector $`\ell`$ and optimal latent furnished by Lemma S1.2, the masked
kernel, defined by the two cases on and off the support,

```math
w_z=
\begin{cases}
\exp(\ell_z\text/3),&z\in S,\\
0,&z\notin S
\end{cases}
\qquad \text{(S1.O)}
```

is feasible in the sense of (C1.1), and each $`q_i`$ is a contact of this same kernel. More generally, for every
$`q\in\Delta_S`$, equality $`\phi(q)=\ell\cdot q`$ holds if and only if $`q`$ is a contact of $`w`$.

*Proof.* We will use Gibbs' inequality including zero probabilities. For any probability laws $`a,b`$ with
$`\mathrm{supp}\,a\subseteq\mathrm{supp}\,b`$, the elementary inequality $`\ln t\le t-1`$ gives

```math
-D(a\Vert b)
=\sum_{z:a(z)>0}a(z)\ln\frac{b(z)}{a(z)}
\le\sum_{z:a(z)>0}\bigl[b(z)-a(z)\bigr]
=\sum_{z:a(z)>0}b(z)-1\le0.
\qquad \text{(S1.P)}
```

Equality requires $`b(z)=a(z)`$ at every positive coordinate of $`a`$ and no $`b`$-mass elsewhere; thus
$`D(a\Vert b)\ge0`$, with equality exactly when $`a=b`$.

Fix arbitrary probability marginals $`u`$ on $`X`$ and $`v`$ on $`Y`$, including marginals with zeros. Define

```math
m(x,y)=w(x,y)u(x)^{2\text/3}v(y)^{2\text/3},\qquad
N_m=\sum_{(x,y)\in S}m(x,y).
\qquad \text{(S1.Q)}
```

Two cases are treated: a zero normalizing mass, and a positive one. If $`N_m=0`$, the desired feasible sum is zero.
If $`N_m>0`$, put $`q=m\text/N_m`$. This is a probability law in $`\Delta_S`$, and $`q(x,y)>0`$ implies $`u(x)>0`$ and
$`v(y)>0`$. At each positive cell,

```math
\ln q(x,y)=\frac{\ell_{xy}}3+\frac23\ln u(x)+\frac23\ln v(y)-\ln N_m,
\qquad
3\sum_{z:q(z)>0}q(z)\ln q(z)
=\ell\cdot q+2\sum_{x:q_X(x)>0}q_X(x)\ln u(x)
 +2\sum_{y:q_Y(y)>0}q_Y(y)\ln v(y)-3\ln N_m.
\qquad \text{(S1.R)}
```

Expand $`\phi`$ using (S1.A) and substitute (S1.R):

```math
\begin{aligned}
\phi(q)-\ell\cdot q
 &=-2\sum_{x:q_X(x)>0}q_X(x)\ln q_X(x)
   -2\sum_{y:q_Y(y)>0}q_Y(y)\ln q_Y(y)
   +3\sum_{z:q(z)>0}q(z)\ln q(z)-\ell\cdot q\\
 &=-3\ln N_m
   -2\sum_{x:q_X(x)>0}q_X(x)\ln\frac{q_X(x)}{u(x)}
   -2\sum_{y:q_Y(y)>0}q_Y(y)\ln\frac{q_Y(y)}{v(y)}\\
 &=-3\ln N_m-2D(q_X\Vert u)-2D(q_Y\Vert v).
\end{aligned}
\qquad \text{(S1.S)}
```

The left side is nonnegative by (S1.F), and both divergences are nonnegative by (S1.P). Therefore
$`3\ln N_m\le-2D(q_X\Vert u)-2D(q_Y\Vert v)\le0`$, so $`N_m\le1`$. This proves feasibility for every $`u,v`$.

Now fix any $`q\in\Delta_S`$ and normalize the kernel at its own marginals:

```math
m_q(x,y)=w(x,y)q_X(x)^{2\text/3}q_Y(y)^{2\text/3},\qquad
N_q=\sum_{(x,y)\in S}m_q(x,y),\qquad
0<N_q\le1.
\qquad \text{(S1.T)}
```

The strict lower bound holds because $`q`$ has a positive cell, where $`w,q_X,q_Y`$ are all positive. Feasibility
gives the upper bound. The law $`q`$ is supported where $`m_q>0`$, so all following logarithms and divergences are
finite. The full expansion is

```math
\begin{aligned}
\ln m_q(x,y)
 &=\ell_{xy}\text/3+(2\text/3)\ln q_X(x)+(2\text/3)\ln q_Y(y)
 \quad(q(x,y)>0),\\
3D(q\Vert m_q\text/N_q)-3\ln N_q
 &=3\sum_{z:q(z)>0}q(z)\ln q(z)
   -3\sum_{z:q(z)>0}q(z)\ln m_q(z)
   +3\ln N_q\sum_zq(z)-3\ln N_q\\
 &=3\sum_{z:q(z)>0}q(z)\ln q(z)-\ell\cdot q
   -2\sum_{x:q_X(x)>0}q_X(x)\ln q_X(x)
   -2\sum_{y:q_Y(y)>0}q_Y(y)\ln q_Y(y)\\
 &=\phi(q)-\ell\cdot q.
\end{aligned}
\qquad \text{(S1.U)}
```

Both $`D(q\Vert m_q\text/N_q)`$ and $`-\ln N_q`$ are nonnegative. Equality of the gap to zero is consequently
equivalent to $`N_q=1`$ and $`q=m_q\text/N_q`$, which is exactly $`q=m_q`$. Conversely, a contact has $`N_q=1`$ and zero
divergence, and hence zero gap. Every $`q_i`$ has zero gap by (S1.N), so it is a contact. Formula (S1.O), rather than the
unmasked exponential off $`S`$, ensures that the common kernel is zero at every missing cell. $`\square`$

Lean: `stoch_to_det.exists_common_contact_pair` (`NaturalLatents/Upstream/Duality.lean`), which returns an attaining
latent, a feasible kernel, and the contact property of every component of positive prior; `stoch_to_det.exists_seedSetup`
(`NaturalLatents/Upstream/Seed.lean`) packages them, with zero priors pruned, as `stoch_to_det.SeedSetup`. The kernel is
$`2^{-\kappa\text/3}`$ for the bit-valued certificate $`\kappa`$ of Lemma S1.2, which equals $`\exp(\ell_z\text/3)`$ on $`S`$. The
Lean differs from the page in three ways:

- **Feasibility.** Instead of normalizing at an arbitrary pair $`u,v`$ as in (S1.Q)–(S1.S), the private
  `valid_iff_feasible` maximizes $`\Lambda(w;u,v)`$ over pairs of probability vectors and applies validity at the
  normalized maximizer, whose marginals are the maximizing pair by the equality case of Young's inequality (the private
  `maximizer_rpow_two_thirds`).
- **The equality case.** The private `Gdef_eq_zero_iff` says that the defect
  $`3\sum_{z:q(z)>0}q(z)\ln\bigl(q(z)\text/m_q(z)\bigr)\text/\ln2`$ (in bits), taken against the unnormalized $`m_q`$,
  vanishes exactly at contacts, and the private `Gdef_eq_certificate_gap` identifies the defect with the certificate
  gap, as in (S1.U); its nonnegativity is `stoch_to_det.Gdef_nonneg`.
- **Masking.** The upstream kernel is not masked: it equals one off $`S`$, which neither `Feasible` nor `IsContact`
  reads. `exists_setup_of_connected` (`NaturalLatents/General/Setup.lean`) replaces it by the masked kernel (S1.O) and
  checks that $`\Lambda`$ is unchanged. `CommonSetup` does not record that $`w`$ vanishes off $`S`$.

**Lemma S1.4 (positivity propagation and the setup on a connected support).** For every finite nonempty $`X,Y`$, every
law $`p`$ with connected support $`S`$, every feasible kernel $`w`$ positive on $`S`$ and zero off $`S`$, and every
contact probability law $`q`$ on $`S`$, one has $`q(z)>0`$ for every $`z\in S`$. In particular, there are a latent attaining $`\tau(p)`$
and a feasible kernel on $`S`$ such that the latent has positive priors, distinct components, each a contact of the
kernel positive on $`S`$, and positive posterior rows throughout $`S`$.

*Proof.* The contact equation and normalization give

```math
\Lambda(w;q_X,q_Y)
=\sum_{(x,y)\in S}w(x,y)q_X(x)^{2\text/3}q_Y(y)^{2\text/3}
=\sum_{z\in S}q(z)=1.
\qquad \text{(S1.V)}
```

Suppose $`q_X(x_0)=0`$, and define

```math
R_0=\sum_{y:(x_0,y)\in S}w(x_0,y)q_Y(y)^{2\text/3}.
\qquad \text{(S1.W)}
```

Two cases are treated: a missing row and a missing column. For the row, if $`R_0>0`$, choose any
$`0<t<\min\{1,R_0^3\}`$ and perturb only the row marginal toward the point mass $`\delta_{x_0}`$ at $`x_0`$. The new marginal is a probability law, and its feasible sum
is

```math
\begin{aligned}
u_t&=(1-t)q_X+t\delta_{x_0},&
\sum_xu_t(x)&=(1-t)\sum_xq_X(x)+t=1,\\
\Lambda(w;u_t,q_Y)
 &=(1-t)^{2\text/3}\Lambda(w;q_X,q_Y)+R_0t^{2\text/3}\\
 &=(1-t)^{2\text/3}+R_0t^{2\text/3}
 \ge1-t+R_0t^{2\text/3}>1.
\end{aligned}
\qquad \text{(S1.X)}
```

The last strict inequality uses $`t<R_0^3`$, which gives $`R_0t^{2\text/3}>t`$. This contradicts feasibility. Hence
$`R_0=0`$ whenever $`q_X(x_0)=0`$. Since every kernel entry on $`S`$ is positive, every edge $`(x,y)\in S`$ with
$`q_Y(y)>0`$ must therefore have $`q_X(x)>0`$.

The column argument is the same calculation with its coordinates displayed. If $`q_Y(y_0)=0`$, put
$`C_0=\sum_{x:(x,y_0)\in S}w(x,y_0)q_X(x)^{2\text/3}`$. Were $`C_0>0`$, for $`0<t<\min\{1,C_0^3\}`$ the probability
marginal $`v_t=(1-t)q_Y+t\delta_{y_0}`$ would satisfy

```math
\sum_yv_t(y)=(1-t)\sum_yq_Y(y)+t=1,\qquad
\Lambda(w;q_X,v_t)
=(1-t)^{2\text/3}+C_0t^{2\text/3}
\ge1-t+C_0t^{2\text/3}>1.
\qquad \text{(S1.Y)}
```

Thus $`C_0=0`$ and each edge with $`q_X(x)>0`$ has $`q_Y(y)>0`$. A probability law $`q`$ has at least one positive
cell, so there are positive row and column vertices from which to start. The two implications propagate positive
marginal mass along every edge of the connected active graph. Every active row and column becomes positive. The
contact equation then gives $`q(z)>0`$ on every cell of $`S`$. For a singleton support this conclusion already holds at
the starting cell.

Apply this result to all components from Lemmas S1.2 and S1.3. For each $`z\in S`$ the posterior row has positive
entries and sums to one:

```math
\pi_i>0,\qquad q_i(z)>0,\qquad
r_z(i)=\frac{\pi_iq_i(z)}{p(z)}>0,\qquad
\sum_i r_z(i)=\frac{\sum_i\pi_iq_i(z)}{p(z)}=1,\qquad
M_L+B_L=\tau(p).
\qquad \text{(S1.Z)}
```

The $`q_i`$ remain pairwise distinct after the merging in (S1.J), and all are contacts of the common feasible kernel
(S1.O). These are exactly the properties of the setup on a connected support. Every posterior assertion is made on
$`S`$, where $`p(z)>0`$. The construction includes unused alphabet coordinates, holes in $`S`$, singleton supports and
$`\tau(p)=0`$; it never divides by $`\tau(p)`$. $`\square`$

Lean: the positivity claim is `stoch_to_det.contact_support_eq` (`NaturalLatents/Upstream/Duality.lean`), stating
`support q = S` for a contact `q` of a feasible kernel on a connected `S`, and the setup is
`exists_setup_of_connected` (`NaturalLatents/General/Setup.lean`), which proves `Nonempty (CommonSetup p)` for every
probability law `p` with connected support:

```lean
theorem exists_setup_of_connected {p : Law X Y} (hp : stoch_to_det.IsPMF p)
    (hconn : stoch_to_det.IsConnected (stoch_to_det.support p)) : Nonempty (CommonSetup p)
```

The structure `CommonSetup` (`NaturalLatents/General/Definitions.lean`) has the fields `L` (the latent), `w` (the
kernel), `feasible`, `attained` ($`M+B=\tau(p)`$), `prior_pos`, `distinct`, `contact`, `positive` and `rows_pos`; the
last seven are the properties in the box above. The Lean differs from the page in four ways:

- **Positivity.** `stoch_to_det.contact_support_eq` does not assume $`w=0`$ off $`S`$, and replaces the perturbations (S1.X) and
  (S1.Y) by the equality case of Young's inequality (the private `maximizer_rpow_two_thirds`) at $`(q_X,q_Y)`$, which
  maximizes $`\Lambda`$ in each argument because $`\Lambda(w;q_X,q_Y)=1`$, so that $`R_0=0`$ exactly when
  $`q_X(x_0)=0`$, and likewise for columns.
- **Propagation.** Positivity is propagated along chains of cells sharing a row or a column (`stoch_to_det.Adj`),
  starting from one positive cell, rather than along the edges of the bipartite graph.
- **Assembly.** `exists_setup_of_connected` takes a `stoch_to_det.SeedSetup` from `stoch_to_det.exists_seedSetup` and a
  `stoch_to_det.Clustering` from `stoch_to_det.exists_clustering`, whose cluster laws are distinct contacts
  (`stoch_to_det.Clustering.Q_isContact`, `stoch_to_det.Clustering.Q_injective`). It then uses
  `setupConn_prior_pos` (cluster masses are positive) and `setupConn_sum_weighted` (cluster sums equal label sums,
  proved from `setupConn_comp_eq_Q`, which identifies each label's law with its cluster's), and `score_nats` with `mediation_add_redundancy_eq_score` to transfer $`M+B=\tau(p)`$ from the seed latent to the merged one.
- **Posterior rows.** `rows_pos` is proved by dividing $`\pi_iq_i(z)>0`$ by $`p(z)>0`$; the row sum in (S1.Z) is not
  stated.
