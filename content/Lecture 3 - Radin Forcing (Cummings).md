# Lecture 3 — Radin Forcing: Factorization and the Prikry Property (Proof)

> [!info] Source
> - **Speaker:** James Cummings
> - **Series:** Simons Semester "Gödel's Program", Banach Center, Warsaw — *Radin Forcing (Lecture 3)*, 1h 05m
> - **Video (local):** `Cummings Lectures/Radin Forcing (Lecture 3).mp4`
> - **Note:** These notes are reconstructed from an automatic transcript, cross-checked against [[Chapter 2 - The Radin Forcing]] (whose numbering and notation are followed) and against [[Lecture 2 - Radin Forcing (Cummings)|Lecture 2]]. This lecture's program: the **factorization** of the forcing below a condition, the **tail-filter** characterization, **Mitchell's genericity criterion**, and the bulk of the session — a **proof of the Prikry property** (by diagonal intersections, no tree argument).
> - **Convention:** the lecture's `length` counts the entry $\kappa$ itself (off by one from [[Chapter 2 - The Radin Forcing|Chapter 2]]); this note follows the Chapter 2 convention (length = number of measures), exactly as in [[Lecture 2 - Radin Forcing (Cummings)#0 ⚠️ Convention mismatch: the meaning of "length"|Lecture 2 §0]].

---

## 1. Warm-up: the Prikry property recalled, and a trivial chain condition

- **Recall** ([[Chapter 2 - The Radin Forcing#^lem-2-4-4|Lemma 2.4.4]]): any sentence of the forcing language can be decided **without touching the stem** — one only trims the constraint sets (a *direct / pure extension* $\leq^*$).
- **Trivial chain condition:** for "completely trivial reasons", $R_{\vec{V}}$ has a reasonable chain condition: two conditions with the **same top** (or the same stem) are compatible simply by **intersecting the measure-one sets at the top**. The dumbest possible reason, but it works: there are only boundedly many stems to worry about.
- Contrast with the Prikry intuition: the point of the Prikry property is that it **does not trivialize** the forcing; it preserves all cardinals below $\kappa$ while doing its work "sideways" (adding the sequence, nothing bounded).

## 2. Direct extensions: shrink, don't add

- A **direct extension** $\leq^*$ is **not allowed to increase the number of entries** in the stem; it only shrinks the large sets.
- How much you can shrink depends on the shape of the condition ("your mileage may vary"):
  - if a stem pair is $(W, B)$ where $W$ actually **carries measures**, then $B$ is only guaranteed large for the **filter** $\bigcap W$ — so shrinking must respect *all* measures of $W$ at once, which needs work (this is exactly where the generalized diagonal intersection of [[Chapter 1 - Measure Sequences#^def-1-3-1|Def 1.3.1]] enters);
  - entries without measures (length $0$ in the Chapter 2 convention) carry empty constraint sets and are inert.

## 3. Factorization: the forcing breaks into low part × high part

**Key feature** (the "self-similarity / local nature" of the definition): *below any reasonable condition, the forcing factors as a product of two forcings*, each a Radin forcing in its own right:

- Take a condition $P$ and an entry $u_i$ of its stem with $\mathrm{length}(u_i) > 0$ (i.e. $u_i$ carries measures — so $R_{u_i}$ is a sensible forcing; see the caveat below).
- **Low part $P^{\mathrm{low}}$:** everything in $P$ at and below $u_i$. The information determining it comes only from $u_i$ and the condition's initial segment — "all of the action in extending a condition is local: anything you want to put between two successive entries is determined by the **top part** of the condition".
- **High part $P^{\mathrm{high}}$:** the rest. It is almost what you expect — a Radin forcing in its own right.
- $R_{\vec{V}} \upharpoonright P$ is (morally) the **product** $P^{\mathrm{low}} \times P^{\mathrm{high}}$; one can choose the splitting point $u_i$ essentially anywhere in the stem.

> [!note] When is $R_U$ "sensible"? (length convention again)
> The lecture is explicit: **"I only really like to define the Radin forcing $R_U$ when the length of $U$ is greater than 1"** (lecture convention), i.e. $\mathrm{length}(U) \geq 1$ in the Chapter 2 convention — "otherwise I write in some stupidity which I wish to avoid". This is the same convention discussion as [[Lecture 2 - Radin Forcing (Cummings)#0 ⚠️ Convention mismatch: the meaning of "length"|Lecture 2 §0]]: a parameter with no measures is degenerate, and the "factorization" statement is only meaningful for entries that are genuine measure sequences. When stating the factorization one truncates to initial segments of length $\geq 1$ so that both factors are legitimate Radin forcings.

**Why factorization is the engine:**
- Each factor still satisfies the Prikry property (so one can iterate the argument).
- **Completeness asymmetry:** the completeness of the measures in the **high** part is far larger than the cardinality of the low part — so repeatedly shrinking large sets (a typical Prikry-property move) never runs out of room. "If you want to shrink repeatedly, you're gonna get in trouble if you don't have enough completeness. But here I have a ton of completeness."

**First payoff (sketched, no full proof):** using the Prikry property + factorization, **bounded subsets of $\kappa$ are generated in a very comprehensible way by the initial segments of the generic sequence** — any bounded new subset lives in the extension generated by a strict initial segment of the generic sequence (the content of [[Chapter 2 - The Radin Forcing#^thm-2-4-5|Theorem 2.4.5]]).

## 4. Anatomy of the generic sequence: successor stages vs limit stages

The generic sequence is a **sequence of measure sequences**, all living below rank $\kappa$, whose critical points form an **increasing, continuous, cofinal sequence** in $\kappa$.

Which kind of object appears at **successor stages** vs **limit stages** is a question of **addability** ([[Chapter 1 - Measure Sequences#^lem-1-4-6|Lemma 1.4.6]]):

- **Successor stages:** a condition establishing that $W$ appears on the generic sequence has a pair $(A, W)$ with the *empty set* at the top of its block — such a $W$ **has no chance of being a limit point** of the generic sequence.
- **Limit stages:** if $\mathrm{length}(W) > 0$ (W carries measures), an easy **density argument involving addability** shows there are unboundedly many candidates to look at — the objects appearing at limit positions are exactly the ones that can be "inserted" there.

**Initial segments are generic.** All reasonable initial segments of a Radin generic sequence are themselves Radin generic — and one can say *which* forcing they are generic for: if $W$ is a measure sequence that occurs on the generic sequence and carries measures, then everything up to (and including) the point $W$ is generic for $R_W$. ("This is critical.")

## 5. The filter at the top = the tail filter of the generic sequence

Fix the parameter $\vec{V}$ with associated filter $F_{\vec{V}} = \bigcap \vec{V}$ (the intersection of all measures on the sequence — *not* the ground-model filter $F_{\kappa,\vec{V}}$). The lecture's "honest wave":

> A set $A \subseteq \kappa$ is in $F_{\vec{V}}$ **iff** it contains a **tail** of the generic sequence.

This is the direct generalization of the favourite Prikry fact: *the normal measure defining Prikry forcing equals the collection of subsets of $\kappa$ containing a tail of the Prikry sequence*.

- **Direction 1 (easy, density):** if $A$ is large and contains a tail, take your favourite condition, intersect the large set into the top, get a stronger condition forcing that on a tail the generic sequence lies inside $A$.
- **Direction 2 (subtle, addability):** if $A \notin F_{\vec{V}}$, then the complement is large for **some** measure $U_\alpha$ of the sequence. By an addability argument, one can take an element of the complement and **add it to the generic sequence** — so the generic sequence hits the complement *cofinally*.

## 6. Mitchell's characterization of genericity (analogue of the Mathias criterion)

**What a "genericity criterion" is.** A Radin generic object is a sequence $X = \langle X_\beta : \beta < \lambda \rangle$ of measure sequences (critical points increasing, continuous, cofinal in $\kappa$). Checking "$X$ meets every dense open set" directly is hopeless; a criterion reduces this to a checkable family of **filter (measure) conditions** — exactly as the Mathias criterion does for Prikry.

**The Prikry template (Mathias).** $X = \langle \alpha_n \rangle$ is Prikry generic over $V$ **iff** for every $A \in U$ (the normal measure), eventually $\alpha_n \in A$. Equivalently: the **tail filter** of $X$, $\{ A \subseteq \kappa : \text{eventually } \alpha_n \in A \}$, equals $U$. Verifying "eventually inside each member of $U$" ⟹ generic for *all* dense open sets.

**The Radin version (Mitchell).** $X$ is generic for $R_{\vec{V}}$ iff:

1. **local genericity** — for each measure sequence $w$ occurring in $X$ with $\mathrm{length}(w) \geq 1$, the part of $X$ below $w$ is generic for $R_w$;
2. **right filter at the top** — $A \in F_{\vec{V}} = \bigcap \vec{V}$ iff $X$ eventually enters $A$ (this is §5);
3. **right tail filter at every limit stage** — for every limit index $\delta$ with limit point $w = X_\delta$, and every $A \in F_w$, the segment of $X$ converging to $w$ eventually enters $A$ (i.e. $\{ \beta < \delta : X_\beta \notin A \}$ is bounded in $\delta$).

(The lecture suspects 2 and 3 suffice; 1 is plausibly redundant — see below.)

**Why this is enough (the recursion).** Take any dense open set $D \subseteq R_{\vec{V}}$. A condition is stem + top set, so $D$'s behaviour is located in one of two places:

- **at the top:** $D$ demands the top set to be chosen from some $A \in F_{\vec{V}}$ — criterion 2 makes $X$ enter $A$ eventually, so $D$ is met;
- **at a limit point** $w = X_\delta$: $D$ demands new stem entries from some $A \in F_w$ — criterion 3 makes the converging segment enter $A$, so $D$ is met.

Criterion 3 at each limit stage supplies the **local Mathias condition** for the sequence below $w$, which (by induction along the ordinals) yields criterion 1 for free; together with criterion 2 at the top, **all** dense open sets are met. ("Really all you gotta do is generate the correct filter.")

**Necessity is trivial:** a generic sequence obviously satisfies 1–3. The point of the criterion: it turns "generic for all dense open sets" into "generates the right filters", which is verifiable inside an ultrapower/iteration — exactly what one uses to certify that the sequences produced by iterated embeddings are generic.

## 7. The proof of the Prikry property (the main event)

The style of proof: **not** a tree argument — "you just keep on taking diagonal intersections until the problem just kind of submits".

### 7.1 The technical lemma (sketch)

Setup: a normal measure sequence $U$, an index $\alpha$ at which a measure occurs, $A$ large for **all** measures of $U$, $E \subseteq A$ large for the **single** measure $U_\alpha$, and a function $F$ defined on a $U_\alpha$-large set, choosing for each measure sequence $w$ a set $F(w)$ large for the **filter** of $w$ (i.e. $F(w) \in \mathcal{F}_w$).

Work on the $j$-side:

1. Since $E$ is large for $U_\alpha$, **$U \upharpoonright \alpha \in j(E)$** (by definition of $U$ as generated from $j$).
2. Apply $j(F)$ to $U \upharpoonright \alpha$: $X := j(F)(U \upharpoonright \alpha)$ is large for all measures of $j(U)$ up to $j(\alpha)$ (the property of $F$ is preserved by elementarity).
3. **Łoś-style membership:** $x \in X$ iff $x \in F(w)$ for $U_\alpha$-many $w$ ("it's an instance of Łoś's theorem at each point of the lights").
4. **Diagonal intersection:** for each $i < \alpha$ take the $X_i$'s and intersect diagonally ([[Chapter 1 - Measure Sequences#^def-1-3-1|Def 1.3.1]]) — producing a set large for every measure with index $< \alpha$.
5. For the measures **after** $\alpha$: a set $Y$ large for $U_\alpha$ which concentrates on "the collection of measure sequences having a measure which concentrates on $Y$" is large for all sorts of subsequent measures; verify by checking $U \upharpoonright \beta \in j(Y)$ (reflection).

The output is a set large for **all** measures of $U$, obtained as Łoś + diagonal intersection + reflection — "a standard Łoś business".

### 7.2 The three cases (the "representative case" + two reductions)

Given a condition and a statement $\phi$, one wants an extension of a **special form** deciding $\phi$; the claim is a **predensity** statement: *every extension of the condition is compatible with an extension of the special form* ("why is there a second direct extension? because all of the action is in the downwards cone below the condition — you can think of it as a dense/predense tissue").

- **Case 1 (representative):** an initial segment of sequences in $X$, followed by a sequence in $Y$. The common extension exists **exactly because of the diagonal intersection**: every $u_i$ ($i<j$) is a member of $X$, and $u_j$ itself is a member of $Y$ — so one can "pull the top of $u_j$ up" past the earlier entries. (*Exercise left to the audience:* write down the formula for a common extension of the three conditions; the worst problem — pulling $u_j$ past the earlier $u_i$'s — is solved precisely by the diagonal conditions.)
- **Case 2:** one stays inside $X$ for a while, then falls into $Z$ — the collection of measure sequences **having a measure which concentrates on $Y$**. This allows **interpolation**: extend the condition by putting in a new entry whose critical point lies between all the previous ones and the next one — possible exactly because $u_j$ carries a measure concentrating on $Y$.
- **Case 3:** everything stays in $X$ — even easier, just **interpolate** using the fact that the measure at index $\alpha$ concentrates on $Y$.

### 7.3 Reduction to a simple condition

Using factorization (§3) + completeness + **power induction** (induction on the length of the sequence), it is enough to prove the Prikry lemma for the very simple condition whose stem is a **single large set**.

**First round (diagonalize):** the standard move — for each low part $s$, if there is a big extension, take it; build the measure-one set in the top of the relevant part by a diagonal section. Payoff: an extension with the "side spine for the remainder"; the effect of the **last** measure-one set on half of the universe has been removed.

**Endgame (sketched, cut short by time):** take more diagonal intersections; arrange an extension which decides $\phi$ using a **minimal number of added points**, then show the last point was not needed — so a *direct* extension suffices. The function $F$ produces a whole bunch of conditions deciding $\phi$; once every extension is compatible with something of the special form, we are done. The lecture ends mid-Case-1 ("I'm sorry to have finished in the middle of the first question"), with a plan change for the next session.

---

## 8. Connections to the Chapters

| Lecture 3 content | Location in the notes |
| --- | --- |
| factorization, high/low parts | [[Chapter 2 - The Radin Forcing#^lem-2-4-2\|Lemma 2.4.2]] (definition is "very local") |
| Prikry property (proof) | [[Chapter 2 - The Radin Forcing#^lem-2-4-4\|Lemma 2.4.4]] |
| bounded subsets of $\kappa$ from initial segments | [[Chapter 2 - The Radin Forcing#^thm-2-4-5\|Theorem 2.4.5]] |
| diagonal intersections as the canonical move | [[Chapter 1 - Measure Sequences#^def-1-3-1\|Def 1.3.1]], [[Chapter 1 - Measure Sequences#^lem-1-4-6\|Lemma 1.4.6]] (addability) |
| length $\geq 1$ for a sensible $R_U$ | [[Lecture 2 - Radin Forcing (Cummings)#0 ⚠️ Convention mismatch: the meaning of "length"\|Lecture 2 §0]] |
| generic sequence = sequence of measure sequences | [[Lecture 2 - Radin Forcing (Cummings)#2 What the generic object is supposed to look like\|Lecture 2 §2]] |
| successor vs limit stages of the generic sequence | [[Chapter 3 - The Radin Club and Changes of Cofinality]] (Radin club) |
| tail filter at the top | [[Chapter 1 - Measure Sequences]] (filters $F_{\vec{V}} = \bigcap \vec{V}$) |

---

## Quick terminology index

| Term | Meaning |
| --- | --- |
| **direct / pure extension** | $\leq^*$: same stem, only large sets shrunk ([[Chapter 2 - The Radin Forcing#^def-2-2-3\|Def 2.2.3]]) |
| **factorization** | below any condition, $R_{\vec{V}}$ ≃ low part × high part, each a Radin forcing ([[Chapter 2 - The Radin Forcing#^lem-2-4-2\|Lemma 2.4.2]]) |
| **low part / high part** | $P^{\mathrm{low}}$: stem at and below some entry $u_i$; $P^{\mathrm{high}}$: the rest |
| **completeness asymmetry** | measures in the high part are complete far beyond the low part — room to shrink repeatedly |
| **tail filter** | $F_{\vec{V}} = \bigcap \vec{V}$; a set is in it iff it contains a tail of the generic sequence (§5) |
| **Mitchell criterion** | local genericity + right tail filter at successor and limit stages ⟹ Radin generic (§6) |
| **Łoś / diagonal intersection** | the two technical ingredients of the Prikry-property proof (§7.1) |
| **interpolation** | inserting a new entry with critical point between the old ones (Cases 2–3) |
