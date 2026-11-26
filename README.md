# 三直径固定为 6 的欧拉图可以有任意大的顶点团覆盖数

AutoGraphForge 候选 `5065dd93` 断言，非平凡欧拉图的顶点团覆盖数至多是三直径加四。完全二部图 $K_{2,12}$ 有 14 个顶点，顶点团覆盖数是 12，三直径是 6。猜想在这张图上会给出 $12\le10$，因而被推翻。Lean 还验证了整个完全二部图族，说明任何只依赖三直径的有限上界都会失败。[Lean 证明](CliqueCover.lean)

[证明](#证明) · [Lean 主文件](CliqueCover.lean) · [查重与先例](audit/search.md)

## 问题出处

Ján Pastorek 的 *AutoGraphForge: Towards Automated Graph Theory Discovery*（2026，arXiv:2609.03478v1）在 §4.2 报告候选及检验结果。本题印在论文配套仓库的候选档案中，ID 为 `5065dd93`。在固定提交 `4d1a8afc99447cacd2328cca20e47b6493e8dbc5` 的规范化审计表里，其总排名为 2441。原始记录的 `status` 为 `proposed`，`lean_statement` 与 `lean_proof` 都为 `null`。[论文](https://arxiv.org/abs/2609.03478v1) · [作者原始档案](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/cegis_results.json) · [固定版本的排名](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/audit_top_normalised.json)

原记录的 `statement` 逐字为

> ((nontrivial) ∧ (eulerian)) ⇒ vertex_clique_cover_number ≤ (triameter + 4)

完整单条 JSON 记录也随项目保存，包括不变量名称、分数和作者记录的证明状态。[原始候选行](audit/source.json)

## 证明

让同一侧的独立顶点越来越多，每个团仍然最多覆盖其中一个。与此同时，任意两点相距至多 2，当独立侧有至少三个顶点时，可以找到三对距离都等于 2 的三点。于是团覆盖数继续增长，三直径停在 6。

顶点团覆盖数 $\theta(G)$ 是将顶点划分成若干团所需的最小团数。三直径 $\operatorname{tr}(G)$ 是对三个不同顶点 $x,y,z$，取三个两两距离之和的最大值。GraphCalc 的实现枚举不同顶点三元组，少于三个顶点时返回零。[GraphCalc 的实现和定义](https://graphcalc.readthedocs.io/en/stable/_modules/graphcalc/graphs/invariants/classics.html) · [Das 对三直径的研究](https://arxiv.org/abs/1804.01088)

令 $G_n=K_{2,n}$，两侧分别为 $\{a_1,a_2\}$ 和 $\{b_1,\ldots,b_n\}$。每个 $a_i$ 与每个 $b_j$ 相邻，同侧两点之间没有边。

1. **欧拉性。** 当 $n>0$ 时图连通。两个 $a_i$ 的度都是 $n$，每个 $b_j$ 的度都是 2。因此每个正偶数 $n$ 都给出连通且各顶点度为偶数的图。
2. **团覆盖数。** 每个团最多包含一个 $b_j$，所以任何划分至少要用 $n$ 个团。若 $n\ge2$，以 $\{a_1,b_1\}$、$\{a_2,b_2\}$ 为两个团，其余 $b_j$ 各自组成单点团，正好用了 $n$ 个。故 $\theta(G_n)=n$。
3. **三直径。** 异侧两点距离为 1，同侧不同两点可经过另一侧的一个点，距离为 2。每个三元组的距离和都至多为 6。若 $n\ge3$，任取三个不同的 $b_j$，它们的三对距离都是 2，故 $\operatorname{tr}(G_n)=6$。

补图提供了另一种核对方式。$\overline{K_{2,n}}$ 是互不相交的 $K_2$ 和 $K_n$，其色数是 $\max(2,n)$，与上面的团覆盖数一致。

取 $n=12$ 即得反例。当 $n=10$ 时等号成立。对任意自然数 $C$，取 $n=2(C+2)$，便得到同样是三直径 6、但顶点团覆盖数严格大于 $C$ 的欧拉图。正偶数 $n=2$ 是三直径公式的边界例子，此时图为四边形，三直径是 4。

## 陈述与代码对照

| 原始对象 | Lean 4 对应 | 核对方式 |
|---|---|---|
| 有限非平凡无向简单图 | `SimpleGraph V`、`[Fintype V]`、`2 ≤ Fintype.card V` | 反例定理直接否定对每个这样的图量化的不等式。 |
| 欧拉图 | `IsEulerian G` | 要求 `G.Connected` 及每个邻点集的基数为偶数。邻点集的基数就是度。 |
| 顶点团覆盖数 | `vertexCliqueCoverNumber G` | 定义为补图可以正确着色的最小颜色数。颜色类恰是原图中的团，正是 GraphCalc 的实现。有限图总能用每个顶点一个颜色着色。 |
| 三直径 | `triameter G` | 枚举有限顶点集的三元组，取三项 `G.dist` 之和的上确界。重复顶点的三元组贡献零，相当于 GraphCalc 对三个不同顶点的枚举。 |
| 见证图 | `exampleGraph 12` | Mathlib 的 `completeBipartiteGraph (Fin 2) (Fin 12)`，直接使用顶点和邻接关系。 |
| 原猜想的否定 | `refute_5065dd93` | 在全称陈述中代入 14 顶点见证，逐一证明全部前提。 |
| 同族的加强结论 | `unbounded_at_six` | 对每个 $C$ 给出满足 $\theta>C$、$\operatorname{tr}=6$ 和欧拉条件的成员。 |

## 候选筛选

同一轮筛选检查了 Pastorek 语料中的三个独立候选。顶点团覆盖候选 `5065dd93` 可以用一个连通完全二部图精确检验，距离与覆盖定义也易于在 Mathlib 中逐项核实，因而入选。燃烧数候选 `fe71fb58` 已有完整反例；色数候选 `f0a6258d` 也已有公开反例，均在查重时排除。[Pastorek 的候选库](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/cegis_results.json) · [燃烧数的在先反例](https://doi.org/10.6084/m9.figshare.33476293.v1) · [色数的在先反例](https://github.com/JanPastorek/AutoGraphForge/issues/1)

## 查重和验证

2026-11-25 核对作者的三个反例档案、作品的前向引用、arXiv、Google Scholar、OpenAlex、DataCite、Figshare、GitHub、MathOverflow、Lean Zulip 及 Mathlib。以原始 ID、原公式和自然语言同义词检索，在可读结果中未发现对这个编号给出完整解答的早期工作。作者其他候选的解答和这里用到的既有图论定义均在查重表中区分列出。此范围的核查不能确定全球首发时间。[逐平台记录与限制](audit/search.md)

使用 Elan 的环境会按 `lean-toolchain` 选择 Lean 4.36.0。Mathlib 固定到 v4.36.0 的提交 `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`。

```sh
lake exe cache get Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex Mathlib.Combinatorics.SimpleGraph.Metric Mathlib.Tactic
lake --wfail build
lake env lean -DwarningAsError=true CliqueCover.lean
lake env leanchecker --verbose CliqueCover
python3 scripts/check.py
```

本项目模块从尚无本项目编译产物的状态构建，构建和内核重放退出码都是 0，严格构建完成 6,422 个 Lake 任务。实际公理输出如下。[构建日志](audit/build.log) · [公理日志](audit/axioms.log) · [内核重放日志](audit/kernel-replay.log)

```text
'CliqueCover.refute_5065dd93' depends on axioms: [propext, Classical.choice, Quot.sound]
'CliqueCover.unbounded_at_six' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Python 脚本对 $n=2,4,\ldots,24$ 从边表作广度优先搜索，枚举所有不同顶点三元组，并用独立集下界及实际的团划分同时验证覆盖数。它先于 Lean 证明运行，全部算术均为整数。[实验日志](audit/examples.log)
