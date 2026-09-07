
Throughout this chapter $\vec{V} = \langle \kappa, U(0), U(1), \dots \rangle \in \mathcal{A}$ is a fixed measure sequence with $\kappa(\vec{V}) = \kappa$ and $\mathrm{length}(\vec{V}) \geq 1$, and $G \subseteq \mathbb{R}_{\vec{V}}$ is generic over $V$. We now study the generic object itself: the set of first coordinates of all stem entries, which turns out to be a closed unbounded subset of $\kappa$ whose order type computes the cofinality of $\kappa$ in $V[G]$.

---

## 3.1 The Radin club

>[!definition] Definition 3.1.1.
>The **Radin club** of $G$ is
>$$C_G = \{\kappa(d) < \kappa \mid \exists p \in G\ (d \text{ appears in the stem of } p)\}.$$
> ^def-3-1-1

>[!lemma] Lemma 3.1.2 (Gitik, Lemma 5.10).
>$C_G$ is a closed unbounded subset of $\kappa$.
> ^lem-3-1-2

*Proof.* **Unbounded.** Let $p = \langle d_1, \dots, d_n, \langle \kappa, \vec{V} \rangle, A \rangle$ and $\tau < \kappa$. Since $A \in \bigcap \vec{V} \subseteq U(0)$ and $U(0)$ concentrates on ordinals, the set of ordinals in $A$ above $\tau$ lies in $U(0)$, hence is nonempty; pick such an ordinal $\nu$ and extend $p$ by appending $\nu$ to the stem. So the conditions forcing a new point of $C_G$ above $\tau$ are dense.

**Closed.** We show that for every $\tau < \kappa$ and every $p$ with $p \Vdash \check{\tau} \notin \dot{C}_G$, some extension of $p$ forces that $\tau$ is not a limit point of $\dot{C}_G$; density then gives closedness in $V[G]$. Write $p = \langle d_1, \dots, d_n, \langle \kappa, \vec{V} \rangle, A \rangle$. Note $\tau \neq \kappa(d_i)$ for all $i$.

*Case 1: $\tau > \kappa(d_n)$.* Set $q = \langle d_1, \dots, d_n, \langle \kappa, \vec{V} \rangle, A \setminus (\tau+1) \rangle \leq^* p$ (removing a bounded set keeps $A$ measure one). Every entry appended later comes from $A \setminus (\tau+1)$, hence lies above $\tau$; every entry inserted below comes from the block of a triple among $d_1, \dots, d_n$, and the contents of such a block lie below its first coordinate $\leq \kappa(d_n) < \tau$; finally, the block of any triple appended later must avoid $V_{\kappa(d_n)+1}$ but is drawn from $A \setminus (\tau+1)$, so it lies above $\tau$ as well. Hence $q \Vdash \sup(\dot{C}_G \cap \check{\tau}) = \kappa(d_n) < \check{\tau}$.

*Case 2: $\tau < \kappa(d_n)$.* Let $i^*$ be least with $\tau < \kappa(d_{i^*+1})$. If $d_{i^*+1}$ is an ordinal, then already $p$ forces that $\dot{C}_G$ has no elements in the interval $(\kappa(d_{i^*}), \tau]$: appended entries lie above $\kappa(d_n) > \tau$, and insertions below $d_{i^*+1}$ must come from the blocks of triples among $d_1, \dots, d_{i^*}$, all of whose contents lie below $\kappa(d_{i^*})$ — in particular there is no block to insert into immediately below an ordinal entry. If $d_{i^*+1} = \langle \nu, \vec{F}_\nu, B_\nu \rangle$ is a triple (so $\tau < \nu$), set $$q = \langle d_1, \dots, d_{i^*}, \langle \nu, \vec{F}_\nu, B_\nu \setminus (\tau+1) \rangle, d_{i^*+2}, \dots, d_n, \langle \kappa, \vec{V} \rangle, A \rangle \leq^* p;$$ this is legitimate since $B_\nu \setminus (\tau+1) \in \bigcap \vec{F}_\nu$ by completeness. Then insertions into the block of $d_{i^*+1}$ lie above $\tau$, insertions into earlier blocks lie below $\kappa(d_{i^*})$, and appended entries lie above $\kappa(d_n) > \tau$; so $q \Vdash \sup(\dot{C}_G \cap \check{\tau}) = \kappa(d_{i^*}) < \check{\tau}$.

In both cases an extension forces $\tau$ not to be a limit of $\dot{C}_G$. $\blacksquare$

The next lemma identifies the limit points of $C_G$; it is the key to every order-type computation that follows.

>[!lemma] Lemma 3.1.3.
>The limit points of $C_G$ are exactly those $\nu$ for which a pair $\langle \nu, \vec{F}_\nu \rangle$ appears (as the first two coordinates of a triple) in the stem of some $p \in G$.
> ^lem-3-1-3

*Proof.* Suppose first that a triple $\langle \langle \nu, \vec{F}_\nu \rangle, B_\nu \rangle$ appears in $p \in G$. Then $\mathrm{length}(\vec{F}_\nu) \geq 1$, so the ordinals of $B_\nu$ form a set in $F_\nu(0)$; as $F_\nu(0)$ is a normal measure on $V_\nu$ concentrating on ordinals, this set is unbounded in $\nu$. Given any $\tau < \nu$, we may extend $p$ by inserting an ordinal of $B_\nu$ above $\tau$ into the block of this triple; hence $p$ forces $\dot{C}_G$ to be cofinal in $\check{\nu}$, and $\nu$ is a limit point of $C_G$.

Conversely, suppose $\nu \in C_G$ is *not* the first coordinate of a pair in any stem. Then $\nu$ appears as an ordinal entry $d_i$ of some $p \in G$. Arguing as in Case 2 of [[#^lem-3-1-2|Lemma 3.1.2]]: entries of $C_G$ below $\nu$ that are added later must be inserted into the blocks of triples among $d_1, \dots, d_{i-1}$, whose contents lie below $\kappa(d_{i-1}) < \nu$ (blocks of triples appended later avoid $V_{\nu+1}$). Hence $$p \Vdash \sup(\dot{C}_G \cap \check{\nu}) \leq \kappa(d_{i-1}) < \check{\nu},$$ and $\nu$ is isolated in $C_G$ from below. $\blacksquare$

>[!corollary] Corollary 3.1.4.
>Parts (a) and (c) of [[Chapter 2 - The Radin Forcing#^prop-2-3-3|Proposition 2.3.3]] hold: in the length-$2$ situation of [[Chapter 2 - The Radin Forcing#^exmp-2-3-2|Example 2.3.2]], $C_G$ is club in $\kappa$, its limit points are exactly the first coordinates of pairs appearing in stems, each such $\nu$ is measurable in $V$, and the points of $C_G$ below such a $\nu$ form (modulo a finite initial segment) a Prikry sequence for the corresponding $F_\nu$.
> ^cor-3-1-4

*Proof.* The club property is [[#^lem-3-1-2|Lemma 3.1.2]]; the identification of limit points is [[#^lem-3-1-3|Lemma 3.1.3]]. For the last clause, apply factorization ([[Chapter 2 - The Radin Forcing#^lem-2-4-2|Lemma 2.4.2]]) below a condition containing the triple at $\nu$: the forcing below $\nu$ is $\mathbb{R}_{\langle \nu, F_\nu \rangle}$, which below the canonical condition is Prikry forcing with $F_\nu$ ([[Chapter 2 - The Radin Forcing#^prop-2-3-1|Proposition 2.3.1]]). $\blacksquare$

---

## 3.2 The order type of $C_G$: sequences of length $<\kappa$

To compute the order type of $C_G$ we stratify the points of $V_\kappa$ according to the length of the measure sequence they carry.

>[!definition] Definition 3.2.1 (Gitik).
>For $0 < \tau < \kappa$ let
>$$X_\tau = \{\langle \nu, \vec{F}_\nu \rangle \mid \vec{F}_\nu \text{ is a sequence of } \nu\text{-complete ultrafilters over } V_\nu \text{ of length } \tau < \nu\},$$
>and set $X_0 = \kappa$ (the ordinals) and $X_\kappa = \{\langle \nu, \vec{F}_\nu \rangle \mid \vec{F}_\nu \text{ has length } \nu\}$.
> ^def-3-2-1

>[!exercise] Exercise 3.2.2.
>Show that the sets $\{X_\tau \mid 0 < \tau < \kappa\}$ are pairwise disjoint and that $X_\tau \in U(\tau)$ for every $\tau$ with $0 < \tau < \mathrm{length}(\vec{V})$. (Hint: in $M$, evaluate $j(X_\tau)$ at $\vec{V} \upharpoonright \tau$, as in [[Chapter 1 - Measure Sequences#^ex-1-2-2|Exercise 1.2.2]].)
> ^ex-3-2-2

>[!lemma] Lemma 3.2.3 (Gitik, Lemma 5.11).
>Suppose $\mathrm{length}(\vec{V}) = \delta$ with $0 < \delta < \kappa$, and let $G \subseteq \mathbb{R}_{\vec{V}}$ be generic. Then in $V[G]$:
>(a) a final segment of $C_G$ has order type $\omega^\delta$ (ordinal exponentiation);
>(b) the condition $\langle \langle \kappa, \vec{V} \rangle, \kappa \cup \bigcup_{0<\tau<\delta} X_\tau \rangle$ forces that the whole of $\dot{C}_G$ has order type $\omega^\delta$;
>(c) if $\delta$ is an uncountable cardinal, then $\mathrm{otp}(C_G) = \delta$.
> ^lem-3-2-3

*Proof.* We prove by induction on $\delta$ the following statement, for every inaccessible $\nu$ and every measure sequence $\vec{F} \in \mathcal{A}$ with $\kappa(\vec{F}) = \nu$ and $\mathrm{length}(\vec{F}) = \delta$: for every generic $h \subseteq \mathbb{R}_{\vec{F}}$, the club $C_h$ has a final segment of order type $\omega^\delta$, and the condition with measure-one set $\nu \cup \bigcup_{0<\tau<\delta} X_\tau$ forces $\mathrm{otp}(\dot{C}_h) = \omega^\delta$. Note that $\nu \cup \bigcup_{0<\tau<\delta} X_\tau \in \bigcap \vec{F}$ by [[#^ex-3-2-2|Exercise 3.2.2]] and upward closure.

*Base $\delta = 1$.* By [[Chapter 2 - The Radin Forcing#^prop-2-3-1|Proposition 2.3.1]] the forcing below the displayed condition is Prikry forcing, and $C_h$ is (modulo finitely many points) the Prikry sequence, of order type $\omega = \omega^1$.

*Inductive step.* Let $\mathrm{length}(\vec{V}) = \delta > 1$ and $G$ generic. Given any $p \in G$, shrink its measure-one set to a subset of $\kappa \cup \bigcup_{0<\tau<\delta} X_\tau$; the analysis below then applies to the final segment of $C_G$ above the stem of $p$, and proves (a) and (b) simultaneously. We use three facts.

**(i) Pair coordinates are cofinal in $\kappa$, with lengths cofinal in $\delta$.** Given a condition $q$ and ordinals $\beta < \kappa$, $\tau < \delta$: the set $A_q \cap X_\tau$ lies in $U(\tau)$, and by the addability lemma ([[Chapter 1 - Measure Sequences#^lem-1-4-6|Lemma 1.4.6]]) we may shrink $A_q$ so that every pair $\langle \nu, \vec{F}_\nu \rangle$ in it satisfies $A_q \cap V_\nu \in \bigcap \vec{F}_\nu$; removing $V_{\beta+1}$ keeps the set in $U(\tau)$. So we may extend $q$ by appending a pair from $X_\tau$ above $\beta$. Density gives both claims.

**(ii) Below a pair coordinate $\nu$ of length $\tau_\nu$, the club looks like $\mathbb{R}_{\vec{F}_\nu}$'s club.** Let $\nu \in C_G$ be a limit point, witnessed by a triple $\langle \langle \nu, \vec{F}_\nu \rangle, B_\nu \rangle$ in $p \in G$ ([[#^lem-3-1-3|Lemma 3.1.3]]), with $\mathrm{length}(\vec{F}_\nu) = \tau_\nu < \delta$. By factorization ([[Chapter 2 - The Radin Forcing#^lem-2-4-2|Lemma 2.4.2]]), the part of the forcing below $\nu$ is $\mathbb{R}_{\vec{F}_\nu}/p^{\leq m}$, and $C_G \cap \nu$ consists of the finitely many stem points of $p$ below $\nu$ together with the Radin club added by the corresponding generic for $\mathbb{R}_{\vec{F}_\nu}$. By the induction hypothesis applied to $\vec{F}_\nu$ (note $\nu < \kappa$ and $\tau_\nu < \delta$), that club has a final segment of order type $\omega^{\tau_\nu}$. Finitely many interleaved extra points do not change the order type $\omega^{\tau_\nu}$ (as $\tau_\nu \geq 1$), so $\mathrm{otp}(C_G \cap \nu) = \omega^{\tau_\nu}$.

**(iii) Between two consecutive pair coordinates there is a run of type $\omega$.** Let $\nu < \nu'$ be consecutive limit points of $C_G$. Every point of $C_G \cap (\nu, \nu')$ is an ordinal ([[#^lem-3-1-3|Lemma 3.1.3]]); the run is infinite, since ordinals from the block of the triple at $\nu'$ (which is unbounded in $\nu'$) can be inserted above any bound by density; and it has no limit point inside $(\nu, \nu')$, again by [[#^lem-3-1-3|Lemma 3.1.3]]. An infinite set of ordinals in $(\nu, \nu')$ whose first limit point is $\nu'$ has order type $\omega$.

Now let $\langle \nu_\xi \mid \xi < \theta \rangle$ increasingly enumerate the limit points of $C_G$. By (i), $\sup_\xi \tau_{\nu_\xi} = \delta$ and the $\nu_\xi$ are cofinal in $\kappa$; by (iii), every point of $C_G$ lies below some $\nu_\xi$, so $C_G = \bigcup_\xi (C_G \cap (\nu_\xi + 1))$, an increasing union of initial segments. By (ii),
$$\mathrm{otp}(C_G \cap (\nu_\xi + 1)) = \omega^{\tau_{\nu_\xi}} + 1,$$
and therefore
$$\mathrm{otp}(C_G) = \sup_{\xi < \theta} \left(\omega^{\tau_{\nu_\xi}} + 1\right) = \omega^{\sup_\xi \tau_{\nu_\xi}} = \omega^\delta,$$
by continuity of $\alpha \mapsto \omega^\alpha$. This proves (a) and (b). For (c): if $\delta$ is an uncountable cardinal, then $\omega^\delta = \sup_{\beta < \delta} \omega^\beta = \delta$, since $|\omega^\beta| = |\beta| < \delta$ for $\beta < \delta$ and the map is continuous. $\blacksquare$

>[!corollary] Corollary 3.2.4.
>[[Chapter 2 - The Radin Forcing#^prop-2-3-3|Proposition 2.3.3]] is now proved in full; in particular, in the length-$2$ example a final segment of $C_G$ has order type $\omega^2$, and $V[G] \models \mathrm{cf}(\kappa) = \omega$.
> ^cor-3-2-4

Combining the order-type computation with cardinal preservation ([[Chapter 2 - The Radin Forcing#^thm-2-4-5|Theorem 2.4.5]]), we obtain the main cofinality theorem.

>[!theorem] Theorem 3.2.5 (Gitik, Theorem 5.12).
>Suppose $\mathrm{length}(\vec{V}) = \delta < \kappa$ is a cardinal, and let $G \subseteq \mathbb{R}_{\vec{V}}$ be generic. Then $V[G]$ is a cardinal-preserving extension of $V$ in which $\kappa$ changes its cofinality to $\mathrm{cf}(\delta)^V$.
> ^thm-3-2-5

*Proof.* Cardinals are preserved by [[Chapter 2 - The Radin Forcing#^thm-2-4-5|Theorem 2.4.5]]. By Lemmas 3.1.2 and 3.2.3, $C_G$ is a closed unbounded subset of $\kappa$ of order type $\omega^\delta$ (a final segment suffices), so $\mathrm{cf}^{V[G]}(\kappa) = \mathrm{cf}(\omega^\delta)$. Finally $\mathrm{cf}(\omega^\delta) = \mathrm{cf}(\delta)$: the map $\xi \mapsto \omega^\xi$ is increasing and continuous, giving $\leq$; and a cofinal sequence in $\omega^\delta$ induces one in $\delta$ via $\alpha \mapsto$ (the least $\beta$ with $\omega^\beta > \alpha$), giving $\geq$. That the cofinality of $\delta$ itself is the same in $V$ and $V[G]$ follows from the Prikry property and the closure of $\leq^*$ by the argument of [[Chapter 2 - The Radin Forcing#^thm-2-4-5|Theorem 2.4.5]]: a name for a shorter cofinal sequence in $\delta$ would yield new bounded subsets of $\kappa$ below a condition all of whose relevant stem points lie above it, which that argument excludes. $\blacksquare$

*Remark (Gitik).* If $\delta > 0$, then $\mathbb{R}_{\vec{V}}$ changes cofinalities also *below* $\kappa$: by [[#^lem-3-1-3|Lemma 3.1.3]] and factorization, every pair coordinate $\nu$ acquires a new club of order type $\omega^{\tau_\nu}$, so new bounded subsets of $\kappa$ appear (this does not contradict the closure arguments above, which apply only below conditions whose stem triples lie above the cardinal in question). Mitchell showed that this is unavoidable from the optimal hypotheses: if the ground model is the core model, then changing the cofinality of $\kappa$ to an uncountable $\delta < \kappa$ while preserving cardinals forces the appearance of new bounded subsets of $\kappa$. On the other hand, with a prepared ground model one can change $\mathrm{cf}(\kappa)$ to an uncountable $\delta$ without adding bounded subsets (Mitchell; a pure forcing construction is due to Gitik). We return to the optimality of hypotheses in Chapter 6.

---

## 3.3 Length $\kappa$ and the general classification

If the sequence is long, the partition of [[#^def-3-2-1|Definition 3.2.1]] becomes fine enough to produce an $\omega$-sequence cofinal in $\kappa$ again.

>[!lemma] Lemma 3.3.1 (Gitik, Lemma 5.13).
>Suppose $\mathrm{length}(\vec{V}) = \kappa$ and $G \subseteq \mathbb{R}_{\vec{V}}$ is generic. Then $V[G] \models \mathrm{cf}(\kappa) = \aleph_0$.
> ^lem-3-3-1

*Proof.* Let $\langle X_\tau \mid \tau < \kappa \rangle$ be the partition of [[#^def-3-2-1|Definition 3.2.1]] and $X = \kappa \cup \bigcup_{\tau < \kappa} X_\tau$; then $X \in \bigcap \vec{V}$ by [[#^ex-3-2-2|Exercise 3.2.2]]. Consider
$$Y = \left\{\langle \nu, \vec{F}_\nu \rangle \in X \ \middle|\ \Bigl(\textstyle\bigcup_{\tau < \mathrm{length}(\vec{F}_\nu)} X_\tau\Bigr) \cap V_\nu \in \textstyle\bigcap \vec{F}_\nu \right\} \cup \kappa.$$
Then $Y \in \bigcap \vec{V}$: for $U(0)$ this is the ordinal part; for $\alpha$ with $0 < \alpha < \kappa$ we check in $M$ that $\vec{V} \upharpoonright \alpha \in j(Y)$. Indeed, the partition computed in $M$ agrees with ours on $V_\kappa$ (since $V_\kappa^M = V_\kappa$), so the defining condition of $j(Y)$ at $\vec{V} \upharpoonright \alpha$ reads $\bigl(\bigcup_{\tau < \alpha} X_\tau\bigr) \cap V_\kappa \in \bigcap_{\beta < \alpha} U(\beta)$; and for each $\beta < \alpha$ this set contains $X_\beta \in U(\beta)$, hence lies in $U(\beta)$ by upward closure.

Pick $p \in G$ whose measure-one set $A$ is contained in $Y$. Let
$$C = \{\langle \nu, \vec{F}_\nu \rangle \in V_\kappa \mid \exists E \in \textstyle\bigcap \vec{F}_\nu\ (\langle \langle \nu, \vec{F}_\nu \rangle, E \rangle \text{ appears in a condition of } G)\},$$
and $C' = \{\nu < \kappa \mid \exists \vec{F}\ (\langle \nu, \vec{F} \rangle \in C)\}$. Then $C \setminus (\kappa(d_n)+1) \subseteq A$, where $d_n$ is the last stem entry of $p$; $C'$ is exactly the set of limit points of $C_G$ ([[#^lem-3-1-3|Lemma 3.1.3]]), hence closed unbounded in $\kappa$; and each $\nu \in C'$ carries a unique $\vec{F}_\nu$ (any two conditions of $G$ are compatible). A density argument as in [[#^lem-3-2-3|Lemma 3.2.3]](i) shows that $C$ contains unboundedly many members of $X_\tau$ for every $\tau < \kappa$.

Define an increasing sequence $\langle \nu_n \mid n < \omega \rangle$ of points of $C'$: let $\nu_0 = \min C'$, and
$$\nu_{n+1} = \min \{\nu \in C' \setminus (\nu_n + 1) \mid \langle \nu, \vec{F}_\nu \rangle \in X_{\nu_n}\},$$
which exists since $C \cap X_{\nu_n}$ is unbounded in $\kappa$. Set $\nu_\omega = \bigcup_{n<\omega} \nu_n$. We claim $\nu_\omega = \kappa$; this gives an $\omega$-sequence cofinal in $\kappa$ and proves the lemma.

Suppose $\nu_\omega < \kappa$. As a limit of points of $C'$, $\nu_\omega$ is a limit point of $C_G$, so $\nu_\omega \in C'$ and there is a unique $\vec{F}$ with $\langle \nu_\omega, \vec{F} \rangle \in C$. Since $C \setminus (\kappa(d_n)+1) \subseteq A \subseteq Y \subseteq X$, this pair lies in $X_\tau$ for a unique $\tau = \mathrm{length}(\vec{F}) < \kappa$. Pick $q \in G$ with $q \leq p$ containing a triple $\langle \langle \nu_\omega, \vec{F} \rangle, B \rangle$. Since $\langle \nu_\omega, \vec{F} \rangle \in Y$ and $\mathrm{length}(\vec{F}) = \tau$, we have $\bigl(\bigcup_{\tau' < \tau} X_{\tau'}\bigr) \cap V_{\nu_\omega} \in \bigcap \vec{F}$, so shrinking $B$ we may assume $B \subseteq \bigcup_{\tau'<\tau} X_{\tau'}$; the shrunk condition is a direct extension of $q$, hence still lies in $G$.

Since $\langle \nu_\omega, \vec{F} \rangle \in X_\tau$, we have $\tau < \nu_\omega = \sup_n \nu_n$. Choose $n$ so large that $\nu_n > \tau$ and $\nu_n$ exceeds every stem entry of $q$ below $\nu_\omega$ (there are only finitely many). We claim that $\langle \nu_{n+1}, \vec{F}_{\nu_{n+1}} \rangle \in B$. Indeed, some condition of $G$ contains a triple at $\nu_{n+1}$ (as $\nu_{n+1} \in C'$); take a common extension $s \in G$ of this condition and $q$. In $s$, the triple at $\nu_{n+1}$ is either inherited from the stem of $q$ or inserted below the triple at $\nu_\omega$. It cannot be inherited: the stem entries of $q$ below $\nu_\omega$ all lie below $\nu_n < \nu_{n+1}$. So it is inserted, and the next old entry of $q$ above $\nu_{n+1}$ is the triple at $\nu_\omega$; by clause (4b) of [[Chapter 2 - The Radin Forcing#^def-2-2-2|Definition 2.2.2]], the insertion comes from the block of that triple, i.e. $\langle \nu_{n+1}, \vec{F}_{\nu_{n+1}} \rangle \in B$.

But then $\langle \nu_{n+1}, \vec{F}_{\nu_{n+1}} \rangle \in B \subseteq \bigcup_{\tau'<\tau} X_{\tau'}$, so $\mathrm{length}(\vec{F}_{\nu_{n+1}}) < \tau < \nu_n$; while by construction $\langle \nu_{n+1}, \vec{F}_{\nu_{n+1}} \rangle \in X_{\nu_n}$, i.e. $\mathrm{length}(\vec{F}_{\nu_{n+1}}) = \nu_n$. This contradicts the disjointness of the $X_\tau$'s. $\blacksquare$

The same ideas give the complete picture for sequences of length $<\kappa^+$.

>[!theorem] Theorem 3.3.2 (Gitik).
>Suppose $\mathrm{length}(\vec{V}) = \delta < \kappa^+$ and $G \subseteq \mathbb{R}_{\vec{V}}$ is generic. Then $\mathbb{R}_{\vec{V}}$ changes the cofinality of $\kappa$, and
>$$\mathrm{cf}^{V[G]}(\kappa) = \begin{cases} \aleph_0, & \delta \text{ a successor ordinal},\\ \mathrm{cf}(\delta)^V, & \delta \text{ a limit and } \mathrm{cf}(\delta) \neq \kappa,\\ \aleph_0, & \mathrm{cf}(\delta) = \kappa. \end{cases}$$
> ^thm-3-3-2

*Proof sketch.* For $\delta < \kappa$ this is contained in [[#^lem-3-2-3|Lemma 3.2.3]] and [[#^thm-3-2-5|Theorem 3.2.5]]: a final segment of $C_G$ has order type $\omega^\delta$, and $\mathrm{cf}(\omega^\delta)$ is $\omega$ for successor $\delta$ and $\mathrm{cf}(\delta)$ for limit $\delta$ (note $\mathrm{cf}(\delta) = \kappa$ is impossible here). For $\delta = \kappa$ this is [[#^lem-3-3-1|Lemma 3.3.1]]. For $\kappa < \delta < \kappa^+$ one repeats the argument of [[#^lem-3-3-1|Lemma 3.3.1]] with a fixed increasing continuous cofinal sequence $\langle \tau_\xi \mid \xi < \mathrm{cf}(\delta) \rangle$ in $\delta$: replace the subfamily $\langle X_{\nu_n} \rangle$ in the construction by $\langle X_{\tau_{\xi}} \rangle$. If $\mathrm{cf}(\delta) = \kappa$, the same recursion produces an $\omega$-sequence cofinal in $\kappa$; if $\mathrm{cf}(\delta) < \kappa$, the pair lengths appearing in $C_G$ are cofinal in $\delta$ of cofinality $\mathrm{cf}(\delta)$, and the induction of [[#^lem-3-2-3|Lemma 3.2.3]] gives a final segment of $C_G$ of order type $\omega^\delta$, whose cofinality is $\mathrm{cf}(\delta)$; the successor case $\delta = \gamma + 1$ is handled by the $\omega$-type run above the last measure $U(\gamma)$, exactly as in [[#^lem-3-2-3|Lemma 3.2.3]](iii). We leave the details as a guided exercise. $\blacksquare$

*Remark.* Note the price of length: changing the cofinality of $\kappa$ to an *uncountable* $\delta$ via $\mathbb{R}_{\vec{V}}$ requires a measure sequence of length at least $\delta$ in $\mathcal{A}$, which by [[Chapter 1 - Measure Sequences#^lem-1-5-1|Lemma 1.5.1]] takes an extender of corresponding strength. Chapters 5 and 6 present the cheaper alternative: coherent sequences of measures and Magidor forcing, which achieve the same cofinality change from Mitchell-order hypotheses alone.

---

## Notes

[[#^lem-3-1-2|Lemma 3.1.2]], [[#^lem-3-2-3|Lemma 3.2.3]], [[#^thm-3-2-5|Theorem 3.2.5]] and [[#^lem-3-3-1|Lemma 3.3.1]] are Gitik's Lemmas 5.10, 5.11, Theorem 5.12 and Lemma 5.13, respectively; [[#^thm-3-3-2|Theorem 3.3.2]] is the classification stated by Gitik immediately after Lemma 5.13. The partition $X_\tau$ of [[#^def-3-2-1|Definition 3.2.1]] is Gitik's, introduced between Lemmas 5.10 and 5.11. [[#^lem-3-1-3|Lemma 3.1.3]] isolates an argument that is implicit in both Gitik's proof of Lemma 5.13 and the analysis of the case $\alpha^* = 2$; together with [[#^lem-3-2-3|Lemma 3.2.3]] it discharges the debt from [[Chapter 2 - The Radin Forcing#^prop-2-3-3|Proposition 2.3.3]]. The remark after [[#^thm-3-2-5|Theorem 3.2.5]] is Gitik's discussion following Theorem 5.12, where Mitchell's results [44, 45] and the pure forcing construction of [13] are cited.


---

## References

Main reference:

- Moti Gitik. Prikry-type forcings. In Matthew Foreman and Akihiro Kanamori, editors, *Handbook of Set Theory*, pages 1351–1447. Springer, Dordrecht, 2010.

Numbering below follows the bibliography of Gitik's chapter:

- [13] Moti Gitik. Changing cofinalities and the nonstationary ideal. *Israel Journal of Mathematics*, 56(3):280–314, 1986.
- [44] William J. Mitchell. Indiscernibles, skies, and ideals. In *Axiomatic Set Theory (Boulder, Colo., 1983)*, volume 31 of Contemporary Mathematics, pages 161–182. American Mathematical Society, Providence, 1984.
- [45] William J. Mitchell. Applications of the covering lemma for sequences of measures. *Transactions of the American Mathematical Society*, 299(1):41–58, 1987.
- [48] Lon B. Radin. Adding closed cofinal sequences to large cardinals. *Annals of Mathematical Logic*, 22(3):243–261, 1982.
