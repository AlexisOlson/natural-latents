# The pair charge

This page proves the pair charge $`PC(23\text/250,7\text/60)`$ of section 0 of the [contact page](contact.md), in
strict form: for every two distinct positive contacts $`P,R`$ of one feasible kernel on a common support $`S`$, holes
allowed,

```math
\frac{I(P)+I(R)}2+\frac{23}{250}\Psi(s)>\frac7{60},\qquad \Psi(s)=-2\ln b(s),\quad b(s)=1-\frac{9s}{16}+\frac{3s^2}{64},
```

with $`s`$ the separation of (C1.3) and $`b`$, $`\Psi`$ as in (A2.1) of the [affinity page](affinity.md). For
$`0<s\le1`$ an entropy payment for one explicit statistic bounds the averaged information below (section 4), and a
scalar certificate closes the charge (section 5); for $`1\le s<2`$ the separation price alone pays. The charge is the
hypothesis $`PC`$ of the mismatch payment, which turns it into $`\gamma d\le(1+2\beta)M+\beta B`$ for the setup latent (step 6 of the
[route](overview.md#the-route)), and its two parameters $`(\beta,\gamma)=(23\text/250,7\text/60)`$
enter the pricing of the constant. In the assembly `NaturalLatents.General.T_le_of_connected`
(`NaturalLatents/General/Pricing.lean`), the `HasPairCharge` hypothesis of `mismatch_payment` (`NaturalLatents/General/Payment.lean`)
is discharged by the pair-charge theorem `pairCharge_C`.

Lemma PC4.0 and Theorem PC5.3 state the standing hypotheses in full; Lemmas PC4.1 to PC4.5 refer to Lemma PC4.0,
and the scalar Lemmas PC5.1 and PC5.2 state their ranges. Unless prefixed `stoch_to_det`, the Lean
declarations named below are in the namespace `NaturalLatents.General`; the `stoch_to_det` declarations are in
`NaturalLatents/Upstream/`, adapted from [DLorell/stoch_to_det](https://github.com/DLorell/stoch_to_det). The Lean proof
of this charge is complete; its declarations are in `NaturalLatents/General/PairCharge.lean` and the modules
`PairCharge/Gram.lean`, `Features.lean`, `MomentBounds.lean`, `Information.lean`, `Correction.lean` and
`Certificate.lean`.

## 4. Pair information from a positive quadratic form

**Setting.** Units and conventions are those of section 0 of the [contact page](contact.md): logarithms are natural and
$`I(P)=D(P\Vert P_X\otimes P_Y)`$ as in (D2). Fix finite nonempty alphabets $`X,Y`$, a nonempty support
$`S\subseteq X\times Y`$ with all rows and columns used, a feasible kernel $`w>0`$ on $`S`$ as in (C1.1), and two distinct
positive contacts $`P,R`$ of $`w`$ as in (C1.2). Extend both laws by zero to the rectangle $`X\times Y`$; its cells outside
$`S`$ are the holes. The fields $`f,g,U,V,A_0,B_0,s,J`$ are those of (C1.3), and an unmarked expectation is under $`P`$.
Every marginal probability of a used symbol is positive, so $`f`$ and $`g`$ are positive and finite on every row and
column, every field below is finite on every cell of the rectangle, holes included, and both contacts have positive
marginals on every used symbol. Put

```math
\begin{aligned}
z&=\frac{A_0-B_0}s,&v&=\frac{A_0B_0}{s^2}=\frac{1-z^2}4,&j&=\frac J{s^2},\\
\eta&=\frac{1+sj}4,&y&=1-s+sj,&t_0&=\frac12-j-\frac32z^2,
\end{aligned}
\qquad
D_X=E[V^2\mid X],\quad D_Y=E[U^2\mid Y].
\qquad \text{(PC4.1)}
```

Some letters are local to this page: $`z`$ is an asymmetry and $`y`$ a scalar, not a cell or a column symbol;
$`w_X,w_Y`$ below are fields, not the kernel $`w`$; $`h`$ below is a cross moment, not the seed entropy $`h`$; unadorned
$`D`$ denotes the integrated variance, while $`D(\cdot\Vert\cdot)`$ denotes relative entropy; $`u`$ is a mixing parameter
and $`v`$ a scalar, not the probability vectors of (C1.1) or the price bound $`u`$ of the [cap page](cap.md);
$`j=J\text/s^2`$ is not the race price $`j(a)`$; $`d_X,d_Y`$ are fields, not the mismatch $`d`$; $`Q`$ is a product law
and $`W`$ a statistic, not the reference $`Q`$ or the winner $`W`$ of the [race page](race.md); $`K(u)`$ in the proof of Lemma PC4.5 is a
relative entropy, not the replica budget $`K`$, and $`\tau`$ in its Lean note is a real parameter; $`F`$, $`F_l`$,
$`F_m`$, $`F_h`$ in section 5 are scalar functions, not the cap $`F`$; $`M_l,M_m,M_h`$ are polynomials, not the budget
$`M`$; and $`\beta,\gamma`$ are the charge pair of section 0 of the contact page, while $`\alpha,\kappa,\lambda,k,c_0`$
are local coefficients.

**Lemma PC4.0 (the moment inputs).** For every finite nonempty $`X,Y`$, every nonempty $`S`$ with all rows and columns used,
every feasible $`w>0`$ on $`S`$, and every pair of distinct positive contacts $`P,R`$ of $`w`$, the quantities (C1.3) and
(PC4.1) satisfy $`0<A_0,B_0<1`$, $`0<s<2`$, $`v\le1\text/4`$,

```math
EU=-A_0,\quad EV=-B_0,\quad EU^2=2A_0-B_0,\quad EV^2=2B_0-A_0,\quad E[UV]=s\eta,\quad E[UV(U+V)]=-J,
\qquad \text{(PC4.M)}
```

and the centered conditionals $`2E[V\mid X]+D_X=U`$ and $`2E[U\mid Y]+D_Y=V`$ on used rows and columns. For every pair of
real marginal fields $`e_X`$ on $`X`$ and $`e_Y`$ on $`Y`$ with $`Ee_X=Ee_Y=0`$,

```math
\mathcal Q(e):=Ee_X^2+Ee_Y^2-4E[e_Xe_Y]\ge0.
\qquad \text{(PC-H)}
```

The fields $`w_X=U+A_0`$, $`w_Y=V+B_0`$, $`d_X=D_X-(2B_0-A_0)`$ and $`d_Y=D_Y-(2A_0-B_0)`$ are centered and satisfy

```math
d_X=w_X-2E[w_Y\mid X],\qquad d_Y=w_Y-2E[w_X\mid Y],
\qquad \text{(PC-C)}
```

and $`\mathcal Q(w)=s^2t_0`$, so that $`t_0\ge0`$, $`j\le1\text/2`$ and $`1\text/16\le\eta^2\le j`$.

*Proof.* Lemma C1.2 gives $`0<s<2`$, and its proof (strict Jensen) gives $`A_0,B_0>0`$; positivity of $`f`$ and $`g`$
gives $`E f>0`$ and $`Eg>0`$, so $`A_0,B_0<1`$. Also $`v=(1-z^2)\text/4\le1\text/4`$. The first four identities of (PC4.M) are the definitions and
(C1.11), and $`E[UV]=(s+J)\text/4=s\eta`$ is (C1.13). Expanding $`g^2=1+2V+V^2`$ in $`E[g^2\mid X]=f=1+U`$ of (C1.4) gives
$`2E[V\mid X]+D_X=U`$, and the mirror argument gives the second conditional. Multiply the first conditional by $`U`$,
the second by $`V`$, average, and use the tower rule, $`E[UD_X]=E[UV^2]`$ and $`E[VD_Y]=E[U^2V]`$:

```math
\begin{aligned}
2E[UV]+E[UV^2]&=EU^2,\qquad 2E[UV]+E[U^2V]=EV^2,\\
4E[UV]+E[UV(U+V)]&=EU^2+EV^2=s,\qquad E[UV(U+V)]=s-4s\eta=-J.
\end{aligned}
```

(PC-H) is the Hessian test (C1.18). The fields are centered because $`EU=-A_0`$, $`EV=-B_0`$, $`ED_X=EV^2=2B_0-A_0`$ and
$`ED_Y=EU^2=2A_0-B_0`$. For (PC-C), $`d_X=U-2E[V\mid X]-2B_0+A_0=(U+A_0)-2(E[V\mid X]+B_0)`$, and the mirror. By (C1.24),

```math
\begin{aligned}
\mathcal Q(w)&=(2A_0-B_0-A_0^2)+(2B_0-A_0-B_0^2)-4(s\eta-A_0B_0)\\
&=s-(A_0^2+B_0^2)-(s+J)+4A_0B_0=6A_0B_0-s^2-J=s^2(6v-1-j)=s^2t_0.
\end{aligned}
```

So (PC-H) at $`e=w`$ gives $`t_0\ge0`$, which is the first inequality of (C1.23), and $`j\le1\text/2-3z^2\text/2\le1\text/2`$.
Cauchy-Schwarz gives $`J=E[(UV)^2]\ge(E[UV])^2=s^2\eta^2`$, so $`j\ge\eta^2`$; and $`J\ge0`$ gives $`\eta\ge1\text/4`$.
$`\square`$

Only the range $`0<s\le1`$ needs the foundation below. For $`1\le s<2`$ the price of section 5 closes the charge.

Lean: `contact_moments` (`NaturalLatents/General/Contact.lean`) supplies the conditional and moment identities of
(C1.4), the energy and quartic identities, $`0<s<2`$ and $`J\le6A_0B_0-s^2`$; the Hessian test (PC-H) is `contact_hessian`
(same file); the identities (PC-C) are
`pairCharge_contact_defect_X` and `pairCharge_contact_defect_Y`, the centering of $`d_X,d_Y`$ is
`pairCharge_contact_defects_centered`, and $`\mathcal Q(w)=6A_0B_0-s^2-J`$ is `pairCharge_contact_gram_energy`, all in
`NaturalLatents/General/PairCharge/Gram.lean`; the bounds on $`j`$ and $`v`$ are `pairCharge_quarticRatio_bounds` and
`defect_bounds` (`NaturalLatents/General/PairCharge/MomentBounds.lean`). The identity $`E[UV(U+V)]=-J`$ is the sum of the
two parts of `pairCharge_secant_mixed_moments` (`MomentBounds.lean`), which states $`E[UV^2]`$ and $`E[U^2V]`$ separately; (PC-C) is stated at used rows and columns, with conditional expectations written as quotients of sums;
and `defect_bounds` also proves $`v\ge2\text/9`$, which this page does not use.

### 4.1 Reversal and a corrected statistic

The reversed orientation takes $`R`$ as reference and $`P`$ as the second contact; its quantities carry a prime. In each
orientation, $`Q`$ is the product of the reference marginals, positive on every cell of the rectangle, and
$`P_u=(1-u)Q+uP`$ (with $`R`$ in place of $`P`$ for the reversed orientation). An overbar averages a quantity over the
two orientations with weight one half; in the reversed orientation $`E_P`$ becomes $`E_R`$ and $`E_Q`$ becomes the
expectation under $`R_X\otimes R_Y`$. Define

```math
\begin{aligned}
W&=\frac{(U+s\text/5)(V+s\text/5)}s,&\Theta&=\frac{D_X+D_Y}s-1,\\
\lambda&=\frac{27-55s}{40},\quad k=13\lambda+2s,\quad c_0=\frac32-\frac s2,&W_u&=W-\lambda u\Theta,\\
\mathrm{Res}&=\overline{\int_0^1(1-u)\mathrm{Var}_{P_u}W_u\,du}.
\end{aligned}
\qquad \text{(PC4.2)}
```

The correction leaves the expectation gap between the contact and the product law unchanged: $`\Theta`$ has zero mean
under both $`P`$ and $`Q`$ (PC4.B), so $`E_PW_u-E_QW_u=E_PW-E_QW`$ for every $`u`$. On $`0<s\le1`$ the Hessian test
(PC-H) then bounds the integrated variance $`\mathrm{Res}`$ by $`\mathrm{Den}(s,j)\text/192`$ (Lemma PC4.4), and
Cauchy–Schwarz turns the gap into the information floor (PC-FLOOR) of Lemma PC4.5.

**Lemma PC4.1 (reversal and raw moments).** Under the hypotheses of Lemma PC4.0,

```math
U'=-\frac Uf,\quad V'=-\frac Vg,\quad D_X'=\frac{D_X}f,\quad D_Y'=\frac{D_Y}g,\quad J'=J,\quad A_0'=B_0,\quad B_0'=A_0,
```

so $`s,j,z^2,v,t_0,\eta,y`$ are common to both orientations. With $`\mu_Q=E_QW`$ and $`\mu_P=E_PW`$,

```math
\begin{aligned}
\mu_Q&=s\left(v-\frac4{25}\right),\qquad \mu_P=\eta-\frac{4s}{25},\\
E_QW^2&=\frac{[(2A_0-B_0)-2sA_0\text/5+s^2\text/25][(2B_0-A_0)-2sB_0\text/5+s^2\text/25]}{s^2},\\
E_PW^2&=\frac{J+(2s\text/5)(-J)+(s^2\text/25)(s+4s\eta)-2s^4\text/125+s^4\text/625}{s^2},
\end{aligned}
\qquad \text{(PC-W)}
```

and in terms of $`s,j,z`$ these read

```math
\mu_Q=\frac{s(1-z^2)}4-\frac{4s}{25},\quad \mu_P=\frac{1+sj}4-\frac{4s}{25},\quad
E_QW^2=\left(\frac12-\frac{4s}{25}\right)^2-z^2\left(\frac32-\frac s5\right)^2,\quad
E_PW^2=j\left(1-\frac s5\right)^2+\frac{2s}{25}-\frac{9s^2}{625}.
```

All four are invariant under reversal.

*Proof.* The reversed ratios are $`1\text/f`$ and $`1\text/g`$, so $`U'=1\text/f-1=-U\text/f`$ and $`V'=-V\text/g`$. By (C1.5)
and the definitions of $`f,g`$, $`R=Pf^2g^2`$ cellwise (both sides vanish at holes), $`R_X=P_Xf^3`$ and $`R_Y=P_Yg^3`$. The
conditional law of $`R`$ on a used row therefore has density $`g^2\text/f`$ relative to that of $`P`$, so
$`D_X'=E[(g^2\text/f)V^2\text/g^2\mid X]=D_X\text/f`$; the mirror gives $`D_Y'`$. Next,
$`J'=E[f^2g^2\cdot U^2V^2\text/(f^2g^2)]=J`$, and $`A_0'=1-E_R[1\text/f]=1-Eg=B_0`$ by (C1.14), and the mirror. Hence
$`s'=s`$, $`z'=-z`$, and every quantity depending on $`s,j,z^2`$ is common.

Under $`Q`$ the fields $`U`$ and $`V`$ are independent with their $`P`$-marginal laws, so
$`\mu_Q=(s\text/5-A_0)(s\text/5-B_0)\text/s=s\text/25-s\text/5+sv`$ and $`E_QW^2`$ factors as displayed, using
$`E(U+s\text/5)^2=EU^2-2sA_0\text/5+s^2\text/25`$. Under $`P`$, (PC4.M) gives
$`\mu_P=(s\eta-s^2\text/5+s^2\text/25)\text/s`$. With $`c=s\text/5`$,

```math
(U+c)^2(V+c)^2=U^2V^2+2cUV(U+V)+c^2(U^2+V^2+4UV)+2c^3(U+V)+c^4,
```

and (PC4.M), with $`EU^2+EV^2=s`$ and $`EU+EV=-s`$, gives $`E_PW^2`$. Substituting $`A_0=s(1+z)\text/2`$,
$`B_0=s(1-z)\text/2`$ and $`J=s^2j`$ gives the second display; reversal replaces $`z`$ by $`-z`$. $`\square`$

Lean: `pairCharge_mean_losses_reverse`, `pairCharge_separation_reverse`, `pairCharge_quarticMoment_reverse`, `pairCharge_quarticRatio_reverse`,
`pairCharge_defectProductRatio_reverse` and `pairCharge_pair_reverse` (`NaturalLatents/General/PairCharge/MomentBounds.lean`) and
`pairCharge_cond_defect_X_reverse`, `pairCharge_cond_defect_Y_reverse`
(`NaturalLatents/General/PairCharge/Features.lean`); `pairCharge_fixed_coefficient_data` (`MomentBounds.lean`) at
coefficient $`1\text/5`$ gives the mean gap and the integrated variance $`D`$ of Lemma PC4.3, from the component moments of
$`UV`$ and $`U+V+s`$ under $`P`$ and $`Q`$ in `pairCharge_fixed_endpoint_table` (`MomentBounds.lean`). Lean does not state
the four raw moments (PC-W) themselves, but states $`D`$ directly in a collected form in $`s,j,v`$, and its statistic is
$`UV\text/s+(U+V+s)\text/5=W+4s\text/25`$, a constant shift that changes no gap, variance or product with $`\Theta`$.

### 4.2 Correction products

In one orientation put

```math
\rho=Ed_X^2+Ed_Y^2,\qquad h=E[d_Xd_Y],\qquad H_0=\frac{UV}s.
```

Since $`d_X+d_Y=D_X+D_Y-s`$, the correction field is $`\Theta=(d_X+d_Y)\text/s`$.

**Lemma PC4.2 (correction products).** Under the hypotheses of Lemma PC4.0, in each orientation,

```math
\begin{aligned}
E[w_Xd_X+w_Yd_Y]&=s^2t_0,\qquad E[w_Xd_Y+w_Yd_X]=\frac{s^2t_0-\rho}2,
&&\text{(PC4.D)}\\
E_P\Theta&=E_Q\Theta=0,\qquad E_Q\Theta^2=\frac\rho{s^2},\qquad E_P\Theta^2=\frac{\rho+2h}{s^2},
&&\text{(PC4.B)}\\
E_Q[(w_X+w_Y)\Theta]+E_P[(w_X+w_Y)\Theta]&=\frac{5s^2t_0-\rho}{2s},
&&\text{(PC4.L)}
\end{aligned}
```

and, averaged over the two orientations,

```math
\overline{E_Q(W\Theta)+E_P(W\Theta)}=j\left(1-\frac s4\right)-\frac14+c_0z^2-\frac{\bar\rho}{10s}.
\qquad \text{(PC-X)}
```

*Proof.* For (PC4.D), multiply the first identity of (PC-C) by $`w_X`$ and the second by $`w_Y`$. Since $`w_X`$ is a function of the
row, $`E[w_XE[w_Y\mid X]]=E[w_Xw_Y]`$, and the mirror holds for columns, so

```math
E[w_Xd_X]+E[w_Yd_Y]=Ew_X^2+Ew_Y^2-4E[w_Xw_Y]=\mathcal Q(w)=s^2t_0
```

by Lemma PC4.0. Multiply instead the first identity of (PC-C) by $`d_X`$ and the second by $`d_Y`$:

```math
Ed_X^2=E[d_Xw_X]-2E[d_Xw_Y],\qquad Ed_Y^2=E[d_Yw_Y]-2E[d_Yw_X],\qquad
\rho=s^2t_0-2E[w_Xd_Y+w_Yd_X].
```

For (PC4.B), $`d_X`$ and $`d_Y`$ are centered marginal fields, and $`Q`$ has the same marginals as $`P`$, so both means of
$`\Theta`$ vanish. Under $`Q`$ they are independent, so $`E_Q(d_X+d_Y)^2=\rho`$; under $`P`$ the cross term is $`2h`$.

For (PC4.L), under $`Q`$ the cross terms $`E_Q[w_Xd_Y]=Ew_X\,Ed_Y`$ and $`E_Q[w_Yd_X]`$ vanish, and a product of two fields of
the same coordinate has the same mean under $`Q`$ and $`P`$, so by (PC4.D)

```math
E_Q[(w_X+w_Y)\Theta]=\frac{E[w_Xd_X+w_Yd_Y]}s=st_0,\qquad
E_P[(w_X+w_Y)\Theta]=\frac{s^2t_0+(s^2t_0-\rho)\text/2}s=\frac{3s^2t_0-\rho}{2s},
```

whose sum is (PC4.L).

The nonlinear product uses one paired change of measure. The mean of $`H_0`$ under $`P`$ is $`E[UV]\text/s=\eta`$. In the
reversed orientation $`H_0'=U'V'\text/s=UV\text/(sfg)`$ and $`\Theta'=(D_X\text/f+D_Y\text/g)\text/s-1`$ by Lemma PC4.1.
Writing the $`R`$-expectation with the density $`f^2g^2`$,

```math
\begin{aligned}
E_P[H_0\Theta]+E_R[H_0'\Theta']
&=\frac{E[UV(D_X+D_Y)]}{s^2}-\frac{E[UV]}s+\frac{E[UV(gD_X+fD_Y)]}{s^2}-\frac{E[UVfg]}s\\
&=\frac{E[UV((1+g)D_X+(1+f)D_Y)]}{s^2}-2\eta,
\end{aligned}
```

because $`fg=1+U+V+UV`$ and (PC4.M) give $`E[UVfg]=s\eta-J+J=s\eta`$. Now $`V(1+g)=g^2-1`$, and $`E[g^2-1\mid X]=f-1=U`$ by
(C1.4), so conditioning on the row gives

```math
E[UV(1+g)D_X]=E[UD_X(g^2-1)]=E[U^2D_X]=E[U^2V^2]=J,
```

the last step by the tower rule. The column mirror is also $`J`$, so the averaged contact product, the half-sum of
$`E_P[H_0\Theta]`$ and its reversed counterpart $`E_R[H_0'\Theta']`$, is $`\overline{E_P(H_0\Theta)}=j-\eta`$. Under $`Q`$, independence gives $`E_Q[UVD_X]=E[UD_X]\,EV`$ and
$`E_Q[UVD_Y]=EU\,E[VD_Y]`$, and the conditionals give $`E[UD_X]=E[U(U-2E[V\mid X])]=EU^2-2E[UV]=2A_0-B_0-2s\eta`$ and
$`E[VD_Y]=2B_0-A_0-2s\eta`$, so

```math
\begin{aligned}
E_Q[UV(D_X+D_Y)]&=-B_0(2A_0-B_0-2s\eta)-A_0(2B_0-A_0-2s\eta)=A_0^2+B_0^2-4A_0B_0+2s^2\eta,\\
E_Q[H_0\Theta]&=\frac{s^2-6A_0B_0+2s^2\eta}{s^2}-\frac{A_0B_0}s=1-6v+2\eta-sv,
\end{aligned}
```

which is common to both orientations. Finally $`W=H_0+(w_X+w_Y)\text/5-4s\text/25`$, and $`\Theta`$ has zero mean under $`P`$
and $`Q`$, so the constant contributes nothing. Adding one fifth of the average of (PC4.L), the left side of (PC-X) is

```math
j-\eta+1-6v+2\eta-sv+\frac{5s^2t_0-\bar\rho}{10s}.
```

Substituting $`v=(1-z^2)\text/4`$, $`\eta=(1+sj)\text/4`$ and $`t_0=1\text/2-j-3z^2\text/2`$, the constants give
$`1\text/4+1-3\text/2=-1\text/4`$, the $`j`$ terms give $`j+sj\text/4-sj\text/2=j(1-s\text/4)`$, the terms in $`s`$ alone
cancel, and the $`z^2`$ terms give $`3z^2\text/2+sz^2\text/4-3sz^2\text/4=c_0z^2`$. This is (PC-X). $`\square`$

Lean: `pairCharge_correction_eq` and `pairCharge_correction_means` (the form and means of $`\Theta`$),
`pairCharge_defect_products` (PC4.D), `pairCharge_correction_second_moments` (PC4.B) and `pairCharge_linear_correction`
(PC4.L), all in `NaturalLatents/General/PairCharge/Correction.lean`, which write $`s^2t_0`$ as $`6A_0B_0-s^2-J`$; and
`pairCharge_statistic_correction_average` (PC-X) (`NaturalLatents/General/PairCharge.lean`), with the statistic
$`W+4s\text/25`$ and $`\bar\rho\text/(10s)`$ written as $`(\rho+\rho')\text/(20s)`$. Its proof uses
`pairCharge_secantStatistic_correction_product` (`NaturalLatents/General/PairCharge/Features.lean`), which states $`E_Q[H_0\Theta]`$ in the
equivalent form $`3z^2\text/2+J\text/(2s)-A_0B_0\text/s`$, and `pairCharge_secantStatistic_correction_joint` (same file), which states the
one-orientation product $`E_P[H_0\Theta]`$ in a form that keeps the terms $`E[UD_X^2]`$ and $`E[VD_Y^2]`$.

### 4.3 Integrated residual

Let

```math
D=\frac{2E_QW^2+E_PW^2}6-\frac{3\mu_Q^2+2\mu_Q\mu_P+\mu_P^2}{12}.
```

**Lemma PC4.3 (the integrated residual).** Under the hypotheses of Lemma PC4.0, with the definitions (PC4.2),

```math
\mathrm{Res}=D-\frac\lambda6\overline{E_Q(W\Theta)+E_P(W\Theta)}+\frac{\lambda^2}{60s^2}\overline{5\rho+6h}.
\qquad \text{(PC-R1)}
```

The fields $`e_X=6\lambda d_X-kw_X`$ and $`e_Y=6\lambda d_Y-kw_Y`$ are centered, and

```math
\mathcal Q(e)=36\lambda^2(\rho-4h)-12\lambda k\rho+k^2s^2t_0.
\qquad \text{(PC-R2)}
```

Consequently

```math
192\,\mathrm{Res}=192D-32\lambda\left[j\left(1-\frac s4\right)-\frac14+c_0z^2\right]+\frac2{15}k^2t_0
-\frac2{15s^2}\overline{\mathcal Q(e)}.
\qquad \text{(PC-R3)}
```

(PC-R1) to (PC-R3) are exact identities; their proof divides only by $`s`$, never by $`\lambda`$, $`\rho`$ or $`h`$.

*Proof.* Under $`P_u`$, the second moment of $`W`$ is $`(1-u)E_QW^2+uE_PW^2`$ and its mean is $`(1-u)\mu_Q+u\mu_P`$.
Integrating with weight $`1-u`$ and the elementary integrals

```math
\int_0^1(1-u)^2du=\frac13,\quad\int_0^1u(1-u)du=\frac16,\quad\int_0^1(1-u)^3du=\frac14,\quad
\int_0^12u(1-u)^2du=\frac16,\quad\int_0^1u^2(1-u)du=\frac1{12}
```

gives $`\int_0^1(1-u)\mathrm{Var}_{P_u}W\,du=D`$, in each orientation; $`D`$ is common to both by Lemma PC4.1. Since
$`\Theta`$ has zero mean under $`P`$ and $`Q`$, it has zero mean under $`P_u`$, so

```math
\mathrm{Var}_{P_u}W_u=\mathrm{Var}_{P_u}W-2\lambda u[(1-u)E_Q(W\Theta)+uE_P(W\Theta)]+\lambda^2u^2[(1-u)E_Q\Theta^2+uE_P\Theta^2].
```

With $`\int_0^1u(1-u)^2du=\int_0^1u^2(1-u)du=1\text/12`$, $`\int_0^1u^2(1-u)^2du=1\text/30`$ and
$`\int_0^1u^3(1-u)du=1\text/20`$, the cross term integrates to $`(\lambda\text/6)[E_Q(W\Theta)+E_P(W\Theta)]`$ and the square
term, by (PC4.B), to $`\lambda^2[\rho\text/30+(\rho+2h)\text/20]\text/s^2=\lambda^2(5\rho+6h)\text/(60s^2)`$. Averaging the
orientations, with $`\lambda`$ and $`D`$ common, gives (PC-R1).

The fields $`e_X,e_Y`$ are centered because $`d_X,d_Y,w_X,w_Y`$ are. By (PC4.D),

```math
\begin{aligned}
Ee_X^2+Ee_Y^2&=36\lambda^2\rho-12\lambda k\,E[w_Xd_X+w_Yd_Y]+k^2(Ew_X^2+Ew_Y^2),\\
E[e_Xe_Y]&=36\lambda^2h-6\lambda k\,E[w_Xd_Y+w_Yd_X]+k^2E[w_Xw_Y],
\end{aligned}
```

and the mixed coefficient in $`\mathcal Q(e)`$ is $`-12\lambda k`$ times
$`E[w_Xd_X+w_Yd_Y]-2E[w_Xd_Y+w_Yd_X]=s^2t_0-(s^2t_0-\rho)=\rho`$, while the $`k^2`$ part is $`k^2\mathcal Q(w)=k^2s^2t_0`$.
This is (PC-R2).

For (PC-R3), substitute (PC-X) into (PC-R1) and multiply by $`192`$:

```math
192\,\mathrm{Res}=192D-32\lambda\left[j\left(1-\frac s4\right)-\frac14+c_0z^2\right]
+\left(\frac{16\lambda^2}{s^2}+\frac{16\lambda}{5s}\right)\bar\rho+\frac{96\lambda^2}{5s^2}\bar h.
```

By (PC-R2), with $`t_0`$ common to both orientations,

```math
\frac2{15s^2}\overline{\mathcal Q(e)}=\frac{24\lambda^2-8\lambda k}{5s^2}\bar\rho-\frac{96\lambda^2}{5s^2}\bar h+\frac2{15}k^2t_0.
```

The coefficients of $`\bar h`$ agree, and with $`k=13\lambda+2s`$ those of $`\bar\rho`$ agree as well:
$`(8\lambda k-24\lambda^2)\text/(5s^2)=(80\lambda^2+16\lambda s)\text/(5s^2)=16\lambda^2\text/s^2+16\lambda\text/(5s)`$. Hence
$`\bar\rho`$ and $`\bar h`$ enter only through $`\overline{\mathcal Q(e)}`$, which is (PC-R3). $`\square`$

Lean: the one-orientation shape of (PC-R1) is the residual in the conclusion of `pairCharge_residual_information`
(`NaturalLatents/General/PairCharge.lean`), with the statistic $`W+4s\text/25`$ and correction $`\Theta`$; the nonnegativity
consequence of (PC-R2) and (PC-H), $`0\le36\lambda^2(\rho-4h)-12\lambda k\rho+k^2s^2t_0`$ for all real $`\lambda,k`$, is
`pairCharge_correction_hessian` (`NaturalLatents/General/PairCharge/Correction.lean`), which does not state the
equality (PC-R2) itself. (PC-R1) with (PC-X)
substituted, (PC-R3) and (PC-R4) below are one statement, `pairCharge_residual_identity`
(`NaturalLatents/General/PairCharge/Certificate.lean`), in the scalars $`s,j,v,\rho,h`$ with $`z^2=1-4v`$, taking $`D`$
in the collected form of `pairCharge_fixed_coefficient_data` at coefficient $`1\text/5`$, which equals (PC-D-RAW)
divided by $`192`$.

### 4.4 A direct residual bound

Define

```math
\begin{aligned}
\mathrm{Den}(s,j)&=15+32j-\left(\frac{178}{25}+\frac{74j}5\right)s+\left(\frac{21}{25}+\frac{46j}{25}-j^2\right)s^2
-32\lambda\left[j\left(1-\frac s4\right)-\frac14\right]+\frac2{15}k^2\left(\frac12-j\right),\\
\Xi&=3-\frac{101}{120}s+\left(\frac7{200}-\frac j{24}\right)s^2+\frac{s^2z^2}{16}.
\end{aligned}
\qquad \text{(PC-DEN)}
```

**Lemma PC4.4 (the residual bound).** Under the hypotheses of Lemma PC4.0,

```math
192D=15+32j-\left(\frac{178}{25}+\frac{74j}5\right)s+\left(\frac{21}{25}+\frac{46j}{25}-j^2\right)s^2-48z^2\Xi,
\qquad \text{(PC-D-RAW)}
```

```math
192\,\mathrm{Res}=\mathrm{Den}(s,j)-z^2\left[48\Xi+32\lambda c_0+\frac{k^2}5\right]-\frac2{15s^2}\overline{\mathcal Q(e)},
\qquad \text{(PC-R4)}
```

and if $`0<s\le1`$, then $`192\,\mathrm{Res}\le \mathrm{Den}(s,j)`$.

*Proof.* (PC-D-RAW) follows by inserting the $`(s,j,z)`$ forms of Lemma PC4.1 into the definition of $`D`$, that is
$`192D=32(2E_QW^2+E_PW^2)-16(3\mu_Q^2+2\mu_Q\mu_P+\mu_P^2)`$, and expanding; it is a polynomial identity in $`s,j,z`$.
The two parts expand separately to

```math
\begin{aligned}
32(2E_QW^2+E_PW^2)&=16+32j-\left(\frac{192}{25}+\frac{64j}5\right)s+\left(\frac{736}{625}+\frac{32j}{25}\right)s^2
-z^2\left(144-\frac{192s}5+\frac{64s^2}{25}\right),\\
16(3\mu_Q^2+2\mu_Q\mu_P+\mu_P^2)&=1-\left(\frac{14}{25}-2j\right)s+\left(\frac{211}{625}-\frac{14j}{25}+j^2\right)s^2
-z^2\left[2s+\left(\frac{22}{25}+2j\right)s^2\right]+3s^2z^4,
\end{aligned}
```

and their difference is (PC-D-RAW): for instance the $`z^2`$ terms give
$`-144+202s\text/5+(2j-42\text/25)s^2`$ and the $`z^4`$ term gives $`-3s^2`$, which are the $`z^2`$ and $`z^4`$ parts
of $`-48z^2\Xi`$.
For (PC-R4), substitute $`t_0=(1\text/2-j)-3z^2\text/2`$ in (PC-R3): the term $`(2\text/15)k^2t_0`$ becomes
$`(2\text/15)k^2(1\text/2-j)-k^2z^2\text/5`$, and (PC-D-RAW) supplies $`-48z^2\Xi`$.

On $`0<s\le1`$, Lemma PC4.0 gives $`j\le1\text/2`$, so $`7\text/200-j\text/24\ge7\text/200-1\text/48=17\text/1200>0`$ and
$`\Xi\ge3-101\text/120=259\text/120`$ for every real $`z`$. Also $`\lambda\ge(27-55)\text/40=-7\text/10`$ and
$`1\le c_0\le3\text/2`$, so $`\lambda c_0\ge-21\text/20`$ (it is nonnegative when $`\lambda\ge0`$). Hence

```math
48\Xi+32\lambda c_0+\frac{k^2}5\ge\frac{518}5-\frac{168}5=70.
```

The Hessian test (PC-H), applied in each orientation to the centered fields $`e_X,e_Y`$ of that orientation's reference
contact, gives $`\overline{\mathcal Q(e)}\ge0`$. Both subtracted terms in (PC-R4) are therefore nonnegative, and
$`192\,\mathrm{Res}\le \mathrm{Den}(s,j)`$. $`\square`$

Lean: `pairCharge_residual_identity` ((PC-R1) with (PC-X) substituted, (PC-R3) and (PC-R4) as one identity, with $`D`$ in the
collected form of `pairCharge_fixed_coefficient_data`, equal to (PC-D-RAW) divided by $`192`$),
`pairCharge_asymmetry_bracket` (the bound $`70`$) and `pairCharge_residual_le_denominator` (the scalar form of the bound),
all in `NaturalLatents/General/PairCharge/Certificate.lean`; the bound for a contact pair is
`pairCharge_residual_bound` (`NaturalLatents/General/PairCharge.lean`), for $`s\le1`$.

### 4.5 Information, support holes and positivity

**Lemma PC4.5 (the information floor).** Under the hypotheses of Lemma PC4.0, if $`0<s\le1`$, then $`\mathrm{Res}>0`$,
$`\mathrm{Den}(s,j)>0`$, and the averaged information $`\bar I=(I(P)+I(R))\text/2`$ satisfies

```math
\bar I\ge\frac{3y^2}{\mathrm{Den}(s,j)}.
\qquad \text{(PC-FLOOR)}
```

*Proof.* The expectation gap is common to both orientations:

```math
\Delta=\mu_P-\mu_Q=\eta-sv=\frac{y+sz^2}4\ge\frac y4,\qquad y=1-s+sj\ge1-\frac{15s}{16}\ge\frac1{16},
```

using $`j\ge1\text/16`$ and $`s\le1`$. Because $`\Theta`$ has zero mean under $`P`$ and $`Q`$, $`W_u`$ has the same gap
$`\Delta`$ for every $`u`$.

Fix one orientation. For $`0\le u<1`$, $`P_u=(1-u)Q+uP`$ is positive on every cell of the rectangle, since $`Q`$ is. Put
$`\chi_u^2=\sum(P-Q)^2\text/P_u`$, the sum over the cells of the rectangle. Since $`\sum(P-Q)=0`$, the gap is $`\Delta=\sum(P-Q)(W_u-E_{P_u}W_u)`$, and Cauchy-Schwarz with weights $`P_u`$
gives

```math
\Delta\le\sqrt{\chi_u^2\,\mathrm{Var}_{P_u}W_u}\qquad(0\le u<1).
```

Let $`K(u)=D(P_u\Vert Q)=\sum Q\,\varphi(P_u\text/Q)`$ with $`\varphi(r)=r\ln r-r+1`$, which is the relative entropy
because $`\sum P_u=\sum Q=1`$, and $`\varphi`$ is continuous on $`[0,\infty)`$ with $`\varphi(0)=1`$. On $`[0,1)`$, $`K`$ is
smooth with

```math
K'(u)=\sum(P-Q)\ln\frac{P_u}Q,\qquad K''(u)=\chi_u^2,\qquad K(0)=K'(0)=0.
```

The formula cannot be evaluated at $`u=1`$ directly: at a hole, $`P=0<Q`$, the cell's term of $`K'(u)`$ is
$`-Q\ln(1-u)`$ and the cell's term of $`\chi_u^2`$ is $`Q\text/(1-u)`$, both unbounded as $`u\to1`$. A limit replaces it.
For $`0<t<1`$, Taylor's formula with integral remainder gives

```math
K(t)=K(0)+tK'(0)+\int_0^t(t-u)K''(u)\,du=\int_0^1(t-u)_+\chi_u^2\,du,
```

where $`(t-u)_+=\max(t-u,0)`$. As $`t`$ increases to $`1`$, the integrand is nonnegative and increases to
$`(1-u)\chi_u^2`$ for every $`u\in[0,1)`$ (the point $`u=1`$ is null), so by monotone convergence the right side tends
to $`\int_0^1(1-u)\chi_u^2\,du`$. The left side tends to $`K(1)=D(P\Vert Q)=I(P)`$, because each cell term
$`Q\,\varphi(P_t\text/Q)`$ is continuous in $`t`$ on $`[0,1]`$. Hence

```math
I(P)=\int_0^1(1-u)\chi_u^2\,du,
```

holes included; at a hole the weight $`1-u`$ cancels the singularity, and the cell contributes $`\int_0^1Q\,du=Q`$. The
same holds in the reversed orientation for $`I(R)`$.

Average the orientations with weight one half and integrate over $`u`$ with weight $`1-u`$. This combined measure has
total mass $`1\text/2`$, the integral of $`\chi_u^2`$ against it is $`\bar I`$, and the integral of
$`\mathrm{Var}_{P_u}W_u`$ against it is $`\mathrm{Res}`$. Integrating the pointwise bound and applying Cauchy-Schwarz for
the integral,

```math
\frac\Delta2\le\sqrt{\bar I\,\mathrm{Res}}.
```

Since $`\Delta>0`$, both $`\bar I`$ and $`\mathrm{Res}`$ are positive. Lemma PC4.4 then gives $`\mathrm{Den}(s,j)\ge192\,\mathrm{Res}>0`$
before any division, and

```math
\bar I\ge\frac{\Delta^2}{4\,\mathrm{Res}}\ge\frac{48\Delta^2}{\mathrm{Den}(s,j)}\ge\frac{3y^2}{\mathrm{Den}(s,j)}.
```

$`\square`$

Lean: `pairCharge_residual_information` (`NaturalLatents/General/PairCharge.lean`) proves, in one orientation and for
any statistic and any correction with zero means under $`P`$ and $`Q`$ and a nonzero gap, that the residual
$`\mathrm{Res}_P`$ of that orientation alone (the integral in (PC4.2) without the average) is positive and
$`\Delta^2\text/(4\,\mathrm{Res}_P)\le I(P)`$, holes allowed; it rests on `pairCharge_entropy_linear_field_affine` and
`pairCharge_entropy_path_payment` (`NaturalLatents/General/PairCharge/Information.lean`), with
`stoch_to_det.joint_absCont_product` (`NaturalLatents/Upstream/ContactInformation.lean`) supplying that $`P`$ vanishes
where $`Q`$ does. The bound $`\Delta\ge y\text/4`$ is `pairCharge_fixed_floor_gap` (`MomentBounds.lean`), the averaging step is
`pairCharge_average_KL_separate` (`PairCharge.lean`), and the division by $`\mathrm{Den}(s,j)`$ is
`pairCharge_projection_information` (`MomentBounds.lean`); the assembled floor is `pairCharge_information_floor`
(`PairCharge.lean`), which states $`\mathrm{Den}(s,j)>0`$ and (PC-FLOOR) for $`s\le1`$. Lean has no integral formula for $`I(P)`$: it proves $`\tau\Delta\le I(P)+\tau^2\,\mathrm{Res}_P`$ in one
orientation for every real $`\tau`$, by a second-derivative comparison on $`[0,1)`$ and continuity at $`u=1`$, and it
combines the two orientations by a reciprocal-mean step on their separate residuals rather than by one Cauchy-Schwarz
over the pooled measure.

## 5. A direct positive scalar certificate

### 5.1 The priced profile

Put

```math
\beta=\frac{23}{250},\quad\gamma=\frac7{60},\quad\alpha=\frac{103}{1000},\quad\kappa=\frac{23}{1000},\qquad
G(s)=\gamma-\alpha s-\kappa s^2.
```

**Lemma PC5.1 (the price).** For $`0\le s\le2`$, $`b(s)>0`$ and

```math
b(s)[\beta\Psi'(s)-\alpha-2\kappa s]=\frac{1071}{64000}\left(s-\frac{170}{1071}\right)^2+\frac{1343}{17136000}
+\frac{69}{32000}s^2(2-s)>0,
\qquad \text{(PC-PRICE)}
```

```math
\beta\Psi(s)\ge\alpha s+\kappa s^2.
\qquad \text{(PC-PRICE-INTEGRAL)}
```

*Proof.* On $`[0,2]`$, $`b'(s)=-9\text/16+3s\text/32<0`$ and $`b(2)=1\text/16`$, so $`b>0`$
(Lemma A2.2 of the [affinity page](affinity.md), (A2.12)). Since
$`\Psi'=-2b'\text/b`$, we have $`b\beta\Psi'=-2\beta b'=207\text/2000-69s\text/4000`$, and

```math
b(s)[\beta\Psi'(s)-\alpha-2\kappa s]=\frac{207}{2000}-\frac{69s}{4000}-\left(\frac{103}{1000}+\frac{23s}{500}\right)b(s)
=\frac1{2000}-\frac{17s}{3200}+\frac{1347s^2}{64000}-\frac{69s^3}{32000}.
```

The right side of (PC-PRICE) expands to the same cubic: its $`s^3`$ coefficient is $`-69\text/32000`$, its $`s^2`$
coefficient $`1071\text/64000+276\text/64000`$, its $`s`$ coefficient $`-340\text/64000`$, and its constant
$`28900\text/68544000+5372\text/68544000=1\text/2000`$. The square and $`s^2(2-s)`$ are nonnegative on $`[0,2]`$ and the
constant is positive, so (PC-PRICE) is positive. Dividing by $`b>0`$, the function $`\beta\Psi(s)-\alpha s-\kappa s^2`$ has
positive derivative on $`[0,2]`$ and vanishes at $`s=0`$, since $`\Psi(0)=0`$; this is (PC-PRICE-INTEGRAL). $`\square`$

Lean: `pairCharge_price` (`NaturalLatents/General/PairCharge/Certificate.lean`) states (PC-PRICE-INTEGRAL) only, for
$`0\le t\le2`$; the identity (PC-PRICE) and $`b>0`$ enter its proof but not its statement.

### 5.2 Three positive quartics

The proof uses explicitly given constants: the shift $`s\text/5`$ in $`W`$, the slope $`\lambda`$, the weight $`k`$,
the profile coefficients $`\alpha,\kappa`$, the polynomials $`M_l,M_m,M_h`$ and the fifteen numerator coefficients below.
Nothing depends on how they were found: every identity below is checked by exact rational arithmetic.

For $`0\le s\le1`$ and $`1\text/16\le j\le1\text/2`$ put $`q=(16j-1)\text/7`$, so $`0\le q\le1`$, and define

```math
\begin{aligned}
F(s,j)&=3(1-s+sj)^2-G(s)\mathrm{Den}(s,j),\qquad F_l(s)=F(s,1\text/16),\qquad F_h(s)=F(s,1\text/2),\\
F_m(s)&=\frac{F_l(s)+F_h(s)}2-\frac{49}{512}[3+G(s)]s^2.
\end{aligned}
```

**Lemma PC5.2 (the scalar certificate).** For $`0\le s\le1`$ and $`1\text/16\le j\le1\text/2`$,

```math
F(s,j)=(1-q)^2F_l(s)+2q(1-q)F_m(s)+q^2F_h(s),
\qquad \text{(PC-INTERPOLATION)}
```

```math
3(1-s+sj)^2-G(s)\mathrm{Den}(s,j)>0.
\qquad \text{(PC-SCALAR)}
```

*Proof.* The coefficient of $`j^2`$ in $`\mathrm{Den}(s,j)`$ is $`-s^2`$, and its other terms are affine in $`j`$. Thus $`F`$ is
quadratic in $`j`$ with $`j^2`$ coefficient $`3s^2+G(s)s^2=[3+G(s)]s^2`$. Substituting $`j=1\text/16+(7\text/16)q`$ gives a
quadratic $`a_0+a_1q+a_2q^2`$ with $`a_2=(49\text/256)[3+G(s)]s^2`$. Any such quadratic equals
$`(1-q)^2a_0+2q(1-q)(a_0+a_1\text/2)+q^2(a_0+a_1+a_2)`$, and its middle coefficient is
$`a_0+a_1\text/2=[F_l+F_h]\text/2-a_2\text/2=F_m`$. This proves (PC-INTERPOLATION); the sign of $`3+G`$ is not needed.

At the two edges,

```math
\mathrm{Den}(s,1\text/16)=\frac{1634669}{64000}-\frac{206141}{6400}s+\frac{574637}{38400}s^2,\qquad
\mathrm{Den}(s,1\text/2)=\frac{128}5-\frac{41}{50}s-\frac{399}{100}s^2,
```

and $`F_l,F_h,F_m`$ are quartics in $`s`$. Define

```math
\begin{aligned}
M_l(s)&=\frac{17}{500}\left(s-\frac34\right)^2+s\left(s-\frac{39}{50}\right)^2\left(\frac{267}{200}+\frac{43}{125}s\right),\\
M_m(s)&=\frac3{20}\left(s-\frac13\right)^2+s\left(s-\frac45\right)^2\left(\frac25+\frac{16}{125}s\right),\\
M_h(s)&=\left(\frac85-\frac{21}{40}s\right)\left(s-\frac1{12}\right)^2+s^3\left[\frac3{1000}+\frac{23}{250}(1-s)\right].
\end{aligned}
```

For $`i\in\{l,m,h\}`$ the certificate is the exact polynomial identity

```math
F_i(s)=M_i(s)+\frac{n_{i0}+n_{i1}s+n_{i2}s^2+n_{i3}s^3+n_{i4}s^4}{d_i},
\qquad \text{(PC-CERTIFICATE)}
```

with these fifteen numerator coefficients:

| i | d_i | n_i0 | n_i1 | n_i2 | n_i3 | n_i4 |
|---|---:|---:|---:|---:|---:|---:|
| l | 2880000000 | 2907750 | 6796995 | 137267 | 6234675 | 528825 |
| m | 1152000000 | 77550 | 106007463 | 57708163 | 5565 | 469995 |
| h | 3600000 | 8000 | 10005 | 116424 | 612 | 828 |

*How to check it by hand.* Substitute $`\lambda=(27-55s)\text/40`$ and $`k=13\lambda+2s`$ into (PC-DEN) at the two edges,
which gives the two quadratics above; form $`F_l`$ and $`F_h`$ from them and $`G`$, and $`F_m`$ from its definition; and
expand $`M_l,M_m,M_h`$. Each identity then reduces to five rational coefficient comparisons, fifteen in all: in every
column below, the coefficient of $`F_i`$ minus that of $`M_i`$ equals $`n_i\text/d_i`$ from the table, shown here in lowest
terms.

| | 1 | s | s^2 | s^3 | s^4 |
|---|---:|---:|---:|---:|---:|
| F_l | 77317/3840000 | 146606221/192000000 | -1059415337/576000000 | 30740153/38400000 | 13216651/38400000 |
| M_l | 153/8000 | 380607/500000 | -1149569/625000 | 19959/25000 | 43/125 |
| n_l/d_l | 3877/3840000 | 453133/192000000 | 137267/2880000000 | 83129/38400000 | 7051/38400000 |
| F_m | 42839/2560000 | 31746607/128000000 | -412399997/1152000000 | 14991731/76800000 | 9861733/76800000 |
| M_m | 1/60 | 39/250 | -5101/12500 | 122/625 | 16/125 |
| n_m/d_m | 517/7680000 | 11778607/128000000 | 57708163/1152000000 | 371/76800000 | 31333/76800000 |
| F_h | 1/75 | -4013/15000 | 10749/6250 | -42983/100000 | -9177/100000 |
| M_h | 1/90 | -173/640 | 27/16 | -43/100 | -23/250 |
| n_h/d_h | 1/450 | 667/240000 | 1617/50000 | 17/100000 | 23/100000 |

Positivity is then checked in two pieces. Every numerator coefficient is positive, so each fraction in (PC-CERTIFICATE) is
positive for $`s\ge0`$. Each $`M_i`$ is a sum of nonnegative terms that cannot vanish together. For $`s\ge0`$, the two
terms of $`M_l`$ are nonnegative; at $`s=0`$ the first is positive, and at a positive zero $`s=3\text/4`$ of the first
square the second square is centered elsewhere, at $`39\text/50`$, so it is positive there. The same argument applies to
$`M_m`$, with centers $`1\text/3`$ and $`4\text/5`$. On $`0\le s\le1`$, the coefficient $`8\text/5-21s\text/40`$ in $`M_h`$
is at least $`43\text/40`$; if $`s>0`$ its last term is at least $`3s^3\text/1000>0`$, and at $`s=0`$ its first term is
positive. Hence $`F_l,F_m,F_h>0`$ on $`[0,1]`$. The interpolation weights $`(1-q)^2`$, $`2q(1-q)`$, $`q^2`$ are
nonnegative and sum to one, so (PC-INTERPOLATION) gives (PC-SCALAR). $`\square`$

Lean: `pairCharge_quartic_low`, `pairCharge_quartic_mid` and `pairCharge_quartic_high`
(`NaturalLatents/General/PairCharge/Certificate.lean`) state the positivity consequences of (PC-CERTIFICATE),
$`F_l>0`$, $`F_m>0`$ and $`F_h>0`$, the first two for $`s\ge0`$ and the third for $`0\le s\le1`$; the certificate
identities appear only in their proofs. `pairCharge_scalar_certificate` (same file) states (PC-SCALAR), with
(PC-INTERPOLATION) used only in its proof. The scalar functions $`G`$, $`\lambda`$, $`k`$, $`\mathrm{Den}(s,j)`$ and $`F`$
are `pairChargeProfile`, `pairChargeSlope`, `pairChargeWeight`, `pairChargeDenominator` and `pairChargeScalar` (same
file).

**Theorem PC5.3 (the pair charge C).** For every finite nonempty $`X,Y`$, every nonempty $`S`$ with all rows and columns
used, every feasible $`w>0`$ on $`S`$, and every pair of distinct positive contacts $`P,R`$ of $`w`$,

```math
\frac{I(P)+I(R)}2+\frac{23}{250}\Psi(s)>\frac7{60}.
```

*Proof.* Lemma PC4.0 gives $`0<s<2`$ and $`1\text/16\le j\le1\text/2`$. If $`0<s\le1`$, Lemma PC4.5 gives $`\mathrm{Den}(s,j)>0`$ at the
actual contact inputs, so (PC-SCALAR) may be divided by $`\mathrm{Den}(s,j)`$, and with (PC-FLOOR)

```math
\bar I\ge\frac{3y^2}{\mathrm{Den}(s,j)}>G(s).
```

Adding (PC-PRICE-INTEGRAL) gives $`\bar I+\beta\Psi(s)>G(s)+\alpha s+\kappa s^2=\gamma`$. If $`1\le s<2`$, nonnegative
information and (PC-PRICE-INTEGRAL) give

```math
\bar I+\beta\Psi(s)\ge\alpha s+\kappa s^2\ge\alpha+\kappa=\frac{63}{500}>\frac7{60},
```

with difference $`7\text/750`$. Thus the strict pair charge holds throughout $`0<s<2`$. $`\square`$

Lean: `pairCharge_C` (`NaturalLatents/General/PairCharge.lean`), stating `HasPairCharge CommonSupportPair (23/250) (7/60)`. It
uses `contact_moments` for $`0<s<2`$ and `pairCharge_price`; for $`s\le1`$, `pairCharge_information_floor`,
`pairCharge_quarticRatio_bounds` and `pairCharge_scalar_certificate`; and for $`s>1`$, `stoch_to_det.Knat_nonneg`
(`NaturalLatents/Upstream/ContactInformation.lean`) for nonnegative information. Lean splits the cases at $`s\le1`$ and
$`s>1`$. Lean's `HasPairCharge` is the non-strict inequality, which the strict one implies.
