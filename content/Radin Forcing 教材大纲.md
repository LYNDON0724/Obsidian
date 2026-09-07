# Radin Forcing 入门小教材 — 大纲

> 依据：Gitik, *Prikry-Type Forcings* (Handbook of Set Theory, Ch. 16) §5.1–5.2；Cummings, IMPAN SimSem 讲义笔记。
> 难度分级：★ = 练习级（可直接验证或留作习题）；★★ = 标准技巧（对角线交、密度论证等，需详细写出）；★★★ = 核心难题（长证明/新技术，需拆成多个引理逐步展开）。

---

## 第 0 章 预备知识（复习性质，可从简）

- 可测基数、正规测度、超幂 $j: V \to M$、crit$(j)$
- Extender 与 $Ult(V, E)$ 的基本事实
- Prikry forcing 回顾：条件、$\le$ 与 $\le^*$、Prikry 性质、不改变基数、$\mathrm{cf}(\kappa) = \omega$
- Mitchell order $o(\kappa)$（用于最后讨论假设的最优性）
```
这些可以先不用写，比较基础
```
---

## 第 1 章 测度序列（Measure Sequences）

### 1.1 需要写明白的定义

1. **由嵌入导出的超滤序列**：设 $j: V \to M$，crit$(j) = \kappa$。递归定义
   - $\mathcal{U}^j(0) = \kappa$（Gitik 记作 $U(0)$：$X \in U(0) \iff \kappa \in j(X)$）；
   - $\mathcal{U}^j(\alpha) = \{A \subseteq V_\kappa \mid \mathcal{U}^j \upharpoonright \alpha \in j(A)\}$，
   - 长度 $\mathrm{lh}(\vec{\mathcal{U}})$ = 最小使 $\vec{\mathcal{U}} \upharpoonright \alpha \notin M$ 的 $\alpha$。
2. **弱测度序列（wms）**：$w(0)$ 不可达；$0 < \alpha < \mathrm{lh}(w)$ 时 $w(\alpha)$ 是 $V_{w(0)}$ 上的测度。记 $\kappa_w = w(0)$。
3. **对角线交**：$\Delta_{x \in \mathcal{I}} A_x = \{w \mid \forall x \in \mathcal{I} \cap V_{\kappa_w}\ (w \in A_x)\}$（这是 Radin 语境下"正确"的对角线交形式）。
4. **测度序列**：存在构造嵌入（constructing embedding）$j$ 使 $w = \mathcal{U}^j \upharpoonright \beta$。
5. **层级**（Cummings 的 $\mathcal{U}_n$ = Gitik 的 $A^{(n)}$）：
   - $\mathcal{U}_0 = \{$所有测度序列$\}$；
   - $\mathcal{U}_{n+1} = \{w \in \mathcal{U}_n \mid$ 每个 $w$ 上的测度集中于 $\mathcal{U}_n\}$；
   - $\mathcal{U}_\infty = \bigcap_{n<\omega} \mathcal{U}_n$（Gitik 记 $\mathcal{A}$）。
6. **过滤器** $\mathcal{F}_w = \bigcap_{0<\alpha<\mathrm{lh}(w)} w(\alpha)$，$\kappa_w$-完备。
```
之后我们写的是全英文版，不要翻译术语了。
```
### 1.2 需要证明的定理

| 编号 | 命题 | 难度 |
|---|---|---|
| Thm 1.1 | 对角线交封闭性：$A_x \in \mathcal{U}^j(\alpha) \Rightarrow \Delta_x A_x \in \mathcal{U}^j(\alpha)$ | ★（留作习题） |
| Thm 1.2 | $\mathcal{U}^j(\alpha)$ 集中于 wms | ★ |
| Thm 1.3 | $\mathcal{U}_\infty$ 的关键性质：$w \in \mathcal{U}_\infty \Rightarrow$ 每个测度集中于 $\mathcal{U}_\infty$ | ★ |
| Lem 1.4 | 设 $u \in \mathcal{U}_\infty$，$A \in \mathcal{F}_u$，则 $B = \{w \in A \mid A \cap V_{\kappa_w} \in \mathcal{F}_w\} \in \mathcal{F}_u$（"可加性"引理，后面 one-step extension 的合法性全靠它） | ★★ |
| Lem 1.5 | （Gitik 5.1）设 $E$ 为 $(\kappa,\lambda)$-extender，$M \supseteq V_{\kappa+2}$，${}^\kappa M \subseteq M$，则 (a) $\mathrm{lh}(\vec{\mathcal{U}}) \ge (2^\kappa)^+$；(b) 对一切 $\alpha < (2^\kappa)^+$，$\vec{\mathcal{U}} \upharpoonright \alpha \in \mathcal{U}_\infty$ | ★★★（需交换图 $V \to M \to N \simeq Ult(M, E')$ 与归纳证明 $U^*(\gamma) = U(\gamma)$，可拆成 2–3 个子引理） |

---

## 第 2 章 Radin Forcing：定义、例子与基本结构性质

（原第 2、3 章合并：定义之后立即分析两个例子，再证明结构性质。）

### 2.1 需要写明白的定义

1. **动机与两个热身情形**（教学上很重要，Gitik 的处理）：
   - $\alpha^* = 1$：$\vec{V} = \langle \kappa, U(0) \rangle$，即普通 Prikry forcing；
   - $\alpha^* = 2$：$\vec{V} = \langle \kappa, U(0), U(1) \rangle$，one-step extension 的两种选择（加序数 / 加 $\langle \nu, F \rangle$ 且要求 $A \cap V_\nu \in F$），产生 $\omega^2$ 型序列。
2. **记号**：$\kappa(d)$（$d$ 为序数 / 对 / 三元组时的第一坐标）；$d \in A$ 指前两个坐标属于 $A$；$\bigcap \vec{F}$。
3. **条件**（Gitik 5.2 = Cummings 的定义）：$p = \langle d_1, \dots, d_n, \langle \kappa, \vec{V} \rangle, A \rangle$ 满足 (1)–(4)（$A \in \bigcap \vec{V}$、$A \subseteq \mathcal{U}_\infty$、交错条件、$A_\nu \cap V_{\kappa(d_i)+1} = \emptyset$ 等）。
4. **序 $\le$**（Gitik 5.3）：嵌入指标 $i_1 < \dots < i_m$、尾部插入与块内插入（4a/4b 两种情形）。
5. **直接扩张 $\le^*$**（Gitik 5.4）：$\le$ 且 $n = m$。
6. **直觉解释**：每个 $d_m = \langle \nu, \vec{F}_\nu, A_\nu \rangle$ 自治地生成一个子 Radin forcing $\mathbb{R}_{\vec{F}_\nu}$。
7. **两个例子**（定义之后的形态分析）：
   - 由一个 measurable cardinal 上一个 normal measure 生成的 Radin forcing：证明其（在 $\mathbf{1}'$ 之下的锥）力迫偏序同构于 Prikry forcing；
   - 由一个 μ-measurable cardinal 生成的长度为 2 的 Radin forcing。

### 2.2 需要证明的定理

（$\le$、$\le^*$ 是偏序、$\le^* \subseteq \le$ 等作为 ★ 习题。）

| 编号      | 命题                                                                                       | 难度                                                                                                                                 |
| ------- | ---------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------- |
| Lem 2.1 | （Gitik 5.5）$\langle \mathbb{R}_{\vec{V}}, \le \rangle$ 满足 $\kappa^+$-c.c.（同茎条件两两相容）               | ★                                                                                                                                  |
| Lem 2.2 | （Gitik 5.6）分解引理：$\mathbb{R}_{\vec{V}}/p \simeq \mathbb{R}_{\vec{V}_m}/p^{\le m} \times \mathbb{R}_{\vec{V}}/p^{>m}$ | ★★                                                                                                                                 |
| Lem 2.3 | （Gitik 5.7）$\langle \mathbb{R}_{\vec{V}}/p^{>m}, \le^* \rangle$ 是 $\nu_m$-闭的                      | ★★                                                                                                                                 |
| Lem 2.4 | （Gitik 5.8）**Prikry 性质**：任意 $p$ 与语句 $\sigma$，存在 $p^* \le^* p$ 决定 $\sigma$                | ★★★（全书核心证明：对每个 $\vec{d}$ 三分 $\tilde{A}(\vec{d})$、按 $U(\alpha)$ 取对角线交 $A(\alpha)$、取最小 $n$ 的反证、三种 Case 讨论；建议拆成"对角线交装置"与"极小长度反证"两个引理） |
| Thm 2.5 | （Gitik 5.9）$V[G]$ 保持所有基数                                                                 | ★★（$\xi > \kappa$ 用 c.c.；$\xi \le \kappa$ 用分解 + 闭性 + Prikry 性质，思路同 Prikry forcing）                                                 |

---

## 第 3 章 Radin Club 与共尾度的改变

```
Club是 Closed and Unbounded 的简称，不能翻译为“俱乐部”啦，注意！
```
### 3.1 需要写明白的定义

1. **Radin Club**：$C_G = \{\kappa(d) < \kappa \mid \exists p \in G\ (d \text{ 出现在 } p \text{ 的有限序列中})\}$。
2. **划分** $X_\tau = \{\langle \nu, \vec{F}_\nu \rangle \mid \mathrm{lh}(\vec{F}_\nu) = \tau\}$（$0 < \tau < \kappa$），外加 $X_0 = \kappa$、$X_\kappa$；各 $X_\tau$ 互不相交且 $X_\tau \in U(\tau)$。

### 3.2 需要证明的定理

| 编号 | 命题 | 难度 |
|---|---|---|
| Lem 3.1 | （Gitik 5.10）$C_G$ 是 $\kappa$ 的闭无界子集 | ★★（无界性：密度；闭性：按 $\tau$ 与 $\kappa(d_i)$ 的相对位置分情形收缩测度一集） |
| Lem 3.2 | （Gitik 5.11）$\mathrm{lh}(\vec{V}) = \delta < \kappa$ 时，$C_G$ 的尾段序型为 $\omega^\delta$（序数幂）；特别地 $\delta$ 为不可数基数时 $\mathrm{otp}(C_G) = \delta$ | ★★（用划分 $X_\tau$ 做归纳） |
| Thm 3.3 | （Gitik 5.12）$\mathrm{lh}(\vec{V}) = \delta < \kappa$ 为基数时，$V[G]$ 保持基数且 $\mathrm{cf}(\kappa) = \mathrm{cf}(\delta)^V$ | ★（由 Thm 2.5 + Lem 3.2 即得） |
| Lem 3.4 | （Gitik 5.13）$\mathrm{lh}(\vec{V}) = \kappa$ 时 $V[G] \models \mathrm{cf}(\kappa) = \aleph_0$ | ★★（构造 $\langle \nu_n \rangle$ 并用 $X_\tau$ 互不相交导出矛盾） |
| Thm 3.5 | 一般情形：$\mathrm{lh}(\vec{V}) = \delta < \kappa^+$ 时共尾度的完整分类（$\delta$ 后继 → $\aleph_0$；$\delta$ 极限且 $\mathrm{cf}(\delta) \ne \kappa$ → $\mathrm{cf}(\delta)$；$\mathrm{cf}(\delta) = \kappa$ → $\aleph_0$） | ★★（与 3.4 同类论证） |

---

## 第 4 章 保持大基数：repeat point 与正则性

### 4.1 需要写明白的定义

1. **Repeat point**（Gitik 5.14）：$\gamma < \mathrm{lh}(\vec{V})$ 使 $\bigcup \vec{V} = \bigcup \vec{V} \upharpoonright \gamma$，即 $\gamma$ 之后的测度不产生新集合。
2. **$\vec{F}$-fat 树**（Gitik 5.16）：$T \subseteq [V_\nu]^{\le n}$，每个非极大节点的后继集属于某个 $F(\alpha)$。
3. **$\eta$-measure one 序列**与 $p^\frown \langle \eta_1, \vec{A}_1 \rangle^\frown \cdots^\frown \langle \eta_m, \vec{A}_m \rangle$ 的记号。

### 4.2 需要证明的定理

| 编号 | 命题 | 难度 |
|---|---|---|
| Prop 4.1 | $2^\kappa = \kappa^+$ 且 $\mathrm{lh}(\vec{V}) = \kappa^{++}$ 时，repeat point 在 $\kappa^{++}$ 中存在（且无界多地 $\vec{U} \upharpoonright \alpha$ 有 repeat point） | ★ |
| Thm 4.2 | （Gitik 5.15）$\gamma$ 为 repeat point $\Rightarrow$ $\kappa$ 在 $V[G]$ 中仍可测 | ★★★（在 $V[G]$ 中定义新超滤 $F$：$\dot{X}[G] \in F \iff$ 某条件在 $M$ 中强迫 $\check{\kappa} \in j(\dot{X})$；需证 well-defined 与正规性，是把 $j$ "提升"的关键论证） |
| Lem 4.3 | （Gitik 5.17）**fat tree 稠密引理**：对稠密开集 $D$ 与 $p$，存在 $p^* \le^* p$ 与 $\vec{F}$-fat 树 $T_k$，使沿任意极大分支 $\eta_k$ 取 measure one 的 $\vec{A}_k$ 都有 $p^* {}^\frown \langle \eta_k, \vec{A}_k \rangle \in D$ | ★★★（5.8 的强化版，按扩张步数 $n$ 归纳构造 $A_n$ 与 $(*)_n$，过程不能在 $\omega$ 步内停则导出矛盾） |
| Thm 4.4 | （Gitik 5.19）$\mathrm{cf}(\mathrm{lh}(\vec{V})) \ge \kappa^+ \Rightarrow$ $\kappa$ 在 $V[G]$ 中保持正则（故不可达） | ★★★（对 $\dot{f}: \check{\delta} \to \check{\kappa}$ 用稠密集 $D_\xi$ + Lem 4.3 + $\mathrm{cf}(\mathrm{lh}) = \kappa^+$ 取 $\alpha$ 压住所有 $\alpha(\vec{d})$，关键 Claim 用分支穿树论证） |
| Rem 4.5 | （Gitik 5.20）4.4 的逆不成立（由 4.2 可知） | ★ |

---

## 第 5 章 Coherent Sequences of Measures 与其上的 Radin Forcing

（Gitik §5.2 前半：5.21–5.24 + p.1419 的总结注记。核心信息：Radin forcing 不必定义在由嵌入导出的测度序列上；Mitchell [42] 证明可以用 coherent sequence 替代嵌入 $j$，从而把大基数假设降到最低并给出 equiconsistency。）

### 5.1 需要写明白的定义

1. **Coherent sequence of measures**（Gitik 5.21，Mitchell [43] 引入）：$\vec{U}$ 是定义在 $\{(\alpha, \beta) \mid \alpha < \ell_{\vec{U}},\ \beta < o^{\vec{U}}(\alpha)\}$ 上的函数，满足
   - $U(\alpha, \beta)$ 是 $\alpha$ 上的正规超滤；
   - **相干性**：若 $j^\alpha_\beta : V \to Ult(V, U(\alpha, \beta))$，则 $j^\alpha_\beta(\vec{U}) \upharpoonright \alpha + 1 = \vec{U} \upharpoonright (\alpha, \beta)$。
2. **用 $\vec{U}(\kappa)$ 替代 $\vec{V}$**：设 $\ell_{\vec{U}} = \kappa + 1$、$o^{\vec{U}}(\kappa) = \delta > 0$，以 $\vec{U}(\kappa) = \langle U(\kappa, \alpha) \mid \alpha < \delta \rangle$ 扮演 $\vec{V}$ 的角色。此时 $A \in \bigcap \vec{U}(\kappa)$ 只含 ordinals；但只要 $o^{\vec{U}}(\nu) > 0$，$\vec{U}(\nu) = \langle U(\nu, \alpha) \mid \alpha < o^{\vec{U}}(\nu) \rangle$ 就是 $\nu$ 上现成的测度序列，且由 $\nu$ 与 $\vec{U}$ 唯一决定。
3. **相干性取代 $\mathcal{A}$**：强调 Gitik 的观察——由 Definition 5.21(2)，不再需要第一章的 $\mathcal{A}$ 层级（也不再需要 constructing embedding / μ-measurable 级别的假设）；讲清楚相干性在反射论证中扮演的角色。
4. **forcing $\mathbb{P}_{\vec{U}}$**（Gitik 5.22–5.24）：条件 $\langle d_1, \dots, d_n, \langle \kappa, A \rangle \rangle$、序 $\le$ 与直接扩张 $\le^*$（表述与 $\mathbb{R}_{\vec{V}}$ 平行，只是 $\vec{F}_\nu$、$\vec{V}$ 从条件中消失）。

### 5.2 需要证明的定理

| 编号      | 命题                                                                                                                                                                                                         | 难度                                                                                       |
| ------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------- |
| Lem 5.1 | $\delta < \kappa$ 时序列可分裂：每个 $U(\kappa, \alpha)$ 集中于 $Y_\alpha = \{\nu < \kappa \mid o^{\vec{U}}(\nu) = \alpha\}$，且各 $Y_\alpha$ 互不相交                                                                        | ★                                                                                        |
| Thm 5.2 | 第 2、3 章的全部结果对 $\mathbb{P}_{\vec{U}}$ 成立（Gitik, p.1419："all the results of the previous section are valid in the present context... proofs require only trivial changes"）：$\kappa^+$-c.c.、分解、闭性、Prikry 性质、基数保持、共尾度分类 | ★★（不一一重复证明，而是指出每处证明中 $\mathcal{A}$ 成员性 / constructing embedding 被相干性替代的确切位置；可作为带提示的系列习题） |

---

## 第 6 章 Magidor Forcing

（Gitik §5.2 后半 + Magidor [37]。作为 $\mathbb{P}_{\vec{U}}$ 的特例得到，故大量性质直接继承第 5 章。）

### 6.1 需要写明白的定义

1. **Magidor forcing 作为 $\mathbb{P}_{\vec{U}}$ 的锥**：$\delta < \kappa$ 时，$\mathbb{P}_{\vec{U}}$ 在条件 $\langle \langle \kappa, \bigcup_{\alpha < \delta} Y_\alpha \rangle \rangle$ 之下就是把 $\mathrm{cf}(\kappa)$ 变为 $\mathrm{cf}(\delta)$ 的 Magidor forcing（Gitik, p.1419）。
2. **等价的直接定义**（Mitchell 递增序列 $\langle U_i \mid i < \delta \rangle$、$o(\kappa) = \delta$）：条件 $(s, \vec{A})$，$s$ 为有限的带下标序数序列 $(\nu, i)$，$\vec{A} = \langle A_i \rangle$、$A_i \in U_i$；扩张与直接扩张。
3. **与 $\mathbb{R}_{\vec{V}}$ 的对比**：测度全部集中于 ordinals、stem 中的点不衍生嵌套 block；说明这正是它只需 $o(\kappa) = \delta$、不需要 μ-measurable 的原因（对照第 1 章 §1.6 的讨论）。

### 6.2 需要证明的定理

| 编号 | 命题 | 难度 |
|---|---|---|
| Thm 6.1 | Magidor forcing 满足 Prikry 性质、保持基数、不加 $\kappa$ 的有界子集，且 $V[G] \models \mathrm{cf}(\kappa) = \mathrm{cf}(\delta)$ | ★（由 Thm 5.2 + Lem 5.1 继承；直接定义的版本可概述证明要点） |
| Rem 6.2 | 假设的最优性（简述不证）：在 core model 中，把 $\kappa$ 的共尾度改为不可数 $\delta < \kappa$ 且保持基数必然加入新的有界子集（Mitchell [45]）；经准备的 ground model 可以避免（Mitchell [44]，纯 forcing 构造见 Gitik [13]）；Magidor 的假设 $o(\kappa) = \delta$ 是最优的 | ★（陈述与讨论） |

---

## 第 7 章 尾声与展望（简述，可不证）

- **Magidor 条件**（Cummings Thm 3，出处为 Cummings 的 IMPAN 讲义笔记（`IMPAN - SimSem - Cummings.md`），非 Handbook 章节——Cummings 的 Handbook 章（Iterated Forcing and Elementary Embeddings）在引言中明确声明不处理 Radin forcing）：$A \in \mathcal{F}_{\mathcal{U}} \iff A$ 包含 generic 序列的尾段；generic 序列的极限点自身是 $\mathbb{R}_{w_\eta}$-generic（交错 generic 结构）。

```
Note: 这个很有用，可以深挖！【在 Gitik 的论文中有提到这个条件】
```

  关联文献：M. Gitik, *Around accumulation points and maximal sequences of indiscernibles* (preprint, 2021)。该文第 3 节把 Magidor 条件拆成两条性质并研究了极大性的成立范围：

  - **(A)（尾段性质）**：设 $o(\kappa) = \delta \leq \kappa$，由 $\vec{U} = \langle U(\kappa, \beta) \mid \beta < \delta \rangle$ 见证；用 $\vec{U}$ 做 Prikry / Magidor / Radin forcing，generic club 为 $C_{\vec{U}}$。则在 $V[C_{\vec{U}}]$ 中，每个 $A \in \bigcap_{\beta < \delta} U(\kappa, \beta)$ 都包含 $C_{\vec{U}}$ 的某条尾段（$C_{\vec{U}} \setminus \eta \subseteq A$）。
  - **(B)（极大性，Maximality）**：任何满足 (A) 的 $C' \subseteq \kappa$，其某条尾段含于 $C_{\vec{U}}$。即 generic club 在所有"几乎含于每个 measure-one 集"的子集中是 $\subseteq^*$-极大的。
  - **Jensen–Dodd–Mitchell**：若 $o(\kappa) < \kappa$ 且 $\kappa$ 改变共尾度，则（core model 背景下）存在同时满足 (A)、(B) 的 club $C \subseteq \kappa$。
  - **Gitik 的定理**：$o(\kappa) = \kappa$ 时 (A) 与 (B) 不可兼得——构造出一个 $\mathrm{cf}(\kappa) = \omega$ 的 generic 扩张，其中不存在同时满足 (A)、(B) 的 club $C \subseteq \kappa$。构造分三步：(i) tree Prikry forcing（从 $\mathbb{R}_{\vec{U}}$ 中提取，产生 Prikry 序列 $\langle \kappa_n \rangle$）；(ii) Easton 支撑的 Prikry/Magidor 迭代，按 $o(\nu)$ 改变每个可测 $\nu \in \kappa \setminus \{\kappa_n\}$ 的共尾度，并把 Mitchell 递增序列转为 Rudin–Keisler 递增序列（视作 extender $E_n$）；(iii) 短 extender forcing。证明对假设满足 (A)+(B) 的 $C$ 分两种情形：若 $C \cap \kappa_n$ 的决定值无限多有界，则造出一条无限次跑出 $C$ 的 indiscernible 序列，否定 (B)；若最终都无界，则用 dominating function + 正规性造出 $A \in \bigcap_\beta U(\kappa, \beta)$ 使 $C$ 中有点无限次跑出 $A$，否定 (A)。
  - **与 Magidor 条件的联系**：Cummings Thm 3 的 "$A \in \mathcal{F}_{\mathcal{U}} \iff A$ 包含 generic 序列的尾段" 正是 (A)+(B) 的滤子表述；Gitik 的结果说明当 $o(\kappa) = \kappa$ 时，这个滤子可能没有"极大代表元"。
  - 该文第 2 节是配套工具：为回答 Mitchell 的问题（$o(\kappa_{i+1}) = \kappa_i$ 的可测序列能否在大模型中配上任意指定的 indiscernible 序列），引入短 extender forcing 的一个变体（用名字补偿 extender 完备性的不足），并证明 accumulation points 的极限在 $K$ 中可以是奇异基数。
  - **Gitik Handbook 章中没有 Radin 版的证明**（已核对 §5.1–5.24）：章内只有 Prikry 情形的原型——Thm 1.12（Mathias [38]：$\omega$-序列 $C$ 是 $U$-Prikry 序列 ⟺ $C$ 几乎含于每个 $A \in U$），其证明经 Lem 1.13（稠密集下的 measure-one 齐次尾段）；而 Lem 5.17（fat tree 引理，教材 Lem 4.3.3）正是 Lem 1.13 的 Radin 强化版，是证明 Radin 版 Magidor 条件的核心工具，但 Gitik 未在章内走出这一步。Radin 版完整证明的来源是 Cummings–Woodin [10]（Cummings 笔记 Thm 3）。若教材第 7 章要写（或概述）Magidor 条件的证明，路线可以是：Lem 1.13（Prikry 原型）→ Lem 4.3.3（fat tree）→ Cummings Thm 3。

- 极大 Radin 序列 / indiscernibles 的存在性问题（Mitchell、Gitik 的结果；Cummings 笔记末尾的 Question）。
- 应用概览：Foreman–Woodin（处处 $2^\tau > \tau^+$）；Cummings（正则处 GCH、奇异处 $2^\tau = \tau^{++}$）；Merimovich 的 extender-based Radin forcing（Gitik §5.3 简介）。

---

## 证明难度的整体评估

- **可以完整写给读者的核心定理**：Lem 2.4（Prikry 性质）、Thm 2.5（基数保持）、Lem 3.1–3.2、Thm 3.3 —— 这是"Radin forcing 改变共尾度而保持基数"的主线。
- **建议完整证明但需拆解的硬证明**：Lem 1.5、Thm 4.2、Lem 4.3、Thm 4.4。
- **适合留作习题**：Thm 1.1–1.3、Lem 2.1、Prop 4.1、第 2 章的偏序验证、Thm 5.2（带提示的翻译练习）。
