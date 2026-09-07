# Note — Genericity Criteria and Maximality: Prikry, Mitchell, Magidor

> [!info] 用途
> 本 Note 汇总"泛型序列的组合刻画"三件套：**Prikry Condition**（文献中称 Mathias criterion）、**Mitchell Criterion**（Radin forcing，Cummings Lecture 3）、**Magidor Generic 的刻画**（Fuchs Theorem 4.4），以及 **Prikry 与 Magidor 泛型序列的 Maximality**。供后续讨论发展。
>
> 主要依据：Mathias [Mat73]；Cummings, *Radin Forcing* Lecture 3（Mitchell criterion，见 [[Lecture 3 - Radin Forcing (Cummings)#6 Mitchell's characterization of genericity (analogue of the Mathias criterion)]]）；Fuchs, *On Sequences Generic in the Sense of Magidor* (2014)。术语与记号沿用 [[Chapter 1 - Measure Sequences]]、[[Chapter 2 - The Radin Forcing]]。

---

## 0. 统一骨架

三种情形共享同一模式：

> **判定"序列是泛型的" ⟺ 两个组合条件：**
> (a) **尾部条件** —— 对相关测度族（滤）的每个成员验证"最终进入"；
> (b) **极限条件** —— 在每个极限点验证一个局部收敛条件。

直接检查"对一切稠密开集泛型"不可行；判据把检查范围化约为"一族滤"（Mathias 判据对 Prikry 的角色，Mitchell 判据对 Radin，Fuchs 定理对 Magidor）。

## 1. Prikry Condition（= Mathias criterion, [Mat73]）

**设置**：κ 可测，$U$ 为 κ 上正规测度，$P_U$ 为 Prikry forcing。

**定理（Mathias, Characterization）。** 设 $c = \langle \alpha_n : n < \omega \rangle$ 递增且共尾于 κ。则 $c$ 对 $P_U$ 在 $V$ 上 generic ⟺ 对每个 $A \in U$（$A \in V$），最终 $\alpha_n \in A$，即 $\operatorname{ran}(c)$ **几乎包含于**每个 $A \in U$。

**等价表述**：$c$ 的**尾部滤** $\{ A \subseteq \kappa : \text{最终 } \alpha_n \in A \}$ 恰好等于 $U$。

- 这是 Prikry 情形的 "Characterization Theorem"：把"对所有稠密开集泛型"化约为"对 $U$ 的成员验证尾部"。
- **迭代版（Solovay 观察）**：迭代 $U$ $\omega$ 次所得临界序列满足该判据，故对直接极限模型 Prikry-generic。

## 2. Mitchell Criterion（Radin forcing）

**设置**：$R_{\vec{V}}$（[[Chapter 2 - The Radin Forcing]]），泛型对象 $X = \langle X_\beta : \beta < \lambda \rangle$ 为**测度序列的序列**（临界点递增、连续、共尾于 κ）。记 $F_w = \bigcap_{\alpha < \mathrm{lh}(w)} w(\alpha)$ 为测度序列 $w$ 的**关联滤**。

**定理（Mitchell；Cummings Lecture 3 表述）。** $X$ 对 $R_{\vec{V}}$ 在 $V$ 上 generic ⟺

1. **局部泛型性**：对出现在 $X$ 中的每个 $w$（$\mathrm{length}(w) \geq 1$），$X$ 在 $w$ 之下的部分对 $R_w$ generic；
2. **顶部正确滤**：$A \in F_{\vec{V}}$ ⟺ $X$ 整体最终进入 $A$；
3. **极限阶段正确滤**：对每个极限指标 $\delta$（极限点 $w = X_\delta$），对每个 $A \in F_w$，$\{ \beta < \delta : X_\beta \notin A \}$ 在 $\delta$ 中有界。

**递归结构**：判据 3 在每个极限点提供"局部 Mathias 条件"，沿极限指标归纳地推出判据 1；判据 2 管最顶端。Cummings 认为 **2 + 3 即充分，1 可能冗余**（"really all you gotta do is generate the correct filter"）。

**类比**：Prikry 情形 = 对角化单个正规测度（Mathias）；Radin 情形 = 在每个极限点对角化局部滤（Mitchell）。详见 [[Lecture 3 - Radin Forcing (Cummings)#6 Mitchell's characterization of genericity (analogue of the Mathias criterion)]] 与 [[Lecture 3 - Radin Forcing (Cummings)#5 The filter at the top = the tail filter of the generic sequence|§5（滤 = 尾部滤）]]。

## 3. Magidor Generic 的刻画（Fuchs Theorem 4.4）

**设置**：$\mathbb{M} = \mathbb{M}\big( \langle U_\gamma : \gamma < \alpha \rangle, \langle f^\nu_\mu : \mu < \nu < \alpha \rangle, \tilde\alpha \big) \in V$，其中：

- $\langle U_\gamma : \gamma < \alpha \rangle$ 是 κ 上 **Mitchell 序递增**的正规超滤序列；
- $f^\nu_\mu$ 见证 $U_\mu \triangleleft U_\nu$，即 $U_\mu = [f^\nu_\mu]_{U_\nu}$；
- $B_\gamma$ 是"Mitchell 序至少 γ 的可测基数"的集合（$c(\gamma)$ 的允许值）；
- $\tilde\alpha$ 为 forcing 的下界参数。

**定理（Fuchs 2014, Characterization）。** 设 $c$ 严格递增且 $c(\gamma) \in B_\gamma \setminus (\tilde\alpha+1)$。则 $c$ 对 $\mathbb{M}$ 在 $V$ 上 generic ⟺

> 1. 对每个 $X \in V \cap \prod_{\gamma<\alpha} U_\gamma$：存在 $\zeta<\alpha$，使对所有 $\xi>\zeta$，$c(\xi) \in X(\xi)$；
> 2. 对每个 $\beta<\alpha$，对每个 $X \in V \cap \prod_{\gamma<\beta} f^\beta_\gamma(c(\beta))$：存在 $\zeta<\alpha$，使对所有 $\xi \in (\zeta,\beta)$，$c(\xi) \in X(\xi)$。

**Remark（Fuchs 4.5，合并形式）**：约定 $c(\alpha) = \kappa$、$f^\alpha_\gamma(\kappa) = U_\gamma$，则 1、2 合并为一条——*对每个 $\beta \le \alpha$，对每个 $X \in \prod_{\gamma<\beta} f^\beta_\gamma(c(\beta))$，尾部进入*。这正是"生成正确的滤"的逐坐标版。

**解读**：
- 条件 1 = **全程尾部滤**：对每个 $U_\gamma$，序列最终进入每个 $X_\gamma$；
- 条件 2 = **极限点收敛**：在极限点 $c(\beta)$ 处，用 Mitchell 序投影 $f^\beta_\gamma(c(\beta))$ 定义局部滤。

**注**：这是 §2 Mitchell criterion 在 Magidor forcing 下的具体化——同一结构，两个家族、两个归名。

## 4. Maximality（极大性）

**Prikry 情形。** 若 $c$ 对 $P_U$ 在 $V$ 上 generic，且 $d \in V[c]$ 也对 $P_U$ generic，则 $\operatorname{ran}(d)$ 几乎包含于 $\operatorname{ran}(c)$。

**Magidor 情形（Fuchs Theorem 6.1, Maximality Theorem）。** 若 $c$ 对 $\mathbb{M}$ 在 $V$ 上 generic，且 $d \in V[c]$ 对（**可能是不同的**）Magidor forcing generic，则 $\operatorname{ran}(d)$ 几乎包含于 $\operatorname{ran}(c)$。若 $d$ 对**同一** $\mathbb{M}$ generic，更强（Fuchs §7, Uniqueness）：对几乎所有 $\xi$，且对所有极限 $\xi$，$c(\xi) = d(\xi)$。

**机制直觉**：组合判据的"尾部进入"条件对泛型序列的 range 是**吸收性**的——任何在扩展 $V[c]$ 中出现的合法序列，其值必须最终落在 $c$ 的 range 内（否则与 $c$ 的滤条件冲突）。因此 $c$ 的 range 是扩展中**最大的不可区分元系统**。Prikry 情形的极大性可由 Mathias 判据 + Solovay 迭代优雅地推出（Fuchs 引言）。

## 5. 结构对照

| 家族 | 判据（归名） | 尾部条件 | 极限条件 | 极大性 |
| --- | --- | --- | --- | --- |
| **Prikry** | Mathias [Mat73] | $\forall A\in U$：尾部进入 | 无真极限点 | $\operatorname{ran}(d) \subseteq^* \operatorname{ran}(c)$ |
| **Radin** | Mitchell（Lecture 3） | 顶部 $F_{\vec{V}}$ | 每个极限点 $w$：$\{X_\beta \notin A\}$ 有界 | 待发展（§6） |
| **Magidor** | Fuchs Thm 4.4 | $\forall U_\gamma$：尾部进入 | 每个 $c(\beta)$：$f^\beta_\gamma$ 投影 | $\operatorname{ran}(d) \subseteq^* \operatorname{ran}(c)$；同 forcing 时逐点相等 |

## 6. 待发展（开放问题）

- **Radin 情形的 Maximality**：Fuchs 的极大性证明依赖 Magidor 判据的组合形式与"沿条件迭代"方法。Radin forcing（Mitchell criterion）是否有同类的极大性/唯一性定理？若有，需要哪种迭代工具？
- **统一抽象**：是否存在统一的 Prikry-type 泛型判据框架（尾部滤 + 极限滤 + 局部泛型性），覆盖 Prikry / Radin / Magidor / extender-based 诸变体？三者的"同构"（§5 表）是否可以在某个范畴/抽象 forcing 语言下精确化？
- **临界序列的泛型性**：三个家族都有"迭代嵌入的临界序列满足判据 ⟹ 对极限模型泛型"（Prikry: Solovay；Magidor: Dehornoy [Deh83] + Fuchs §5；Radin: Lecture 5/§5 迭代构造）。统一叙述与证明是什么？

## 参考文献

- A. R. D. Mathias, *On sequences generic in the sense of Prikry*, J. Austral. Math. Soc. **15** (1973), 409–414. [Mat73]
- M. Magidor, *Changing cofinality of cardinals*, Fund. Math. **99** (1978), 61–71. [Mag78]
- P. Dehornoy, 1983（临界序列的 Magidor-泛型性，树版本；见 Fuchs 2014 引言）。[Deh83]
- G. Fuchs, *On Sequences Generic in the Sense of Magidor*, 2014. https://www.math.csi.cuny.edu/~fuchs/MagidorSequences.pdf
- J. Cummings, *Radin Forcing* Lecture 3, Simons Semester "Gödel's Program", Banach Center（Mitchell criterion 的表述）。[[Lecture 3 - Radin Forcing (Cummings)]]
- M. Gitik, *Prikry-Type Forcings*, in Handbook of Set Theory, Ch. 5（背景）。
