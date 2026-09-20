# JSP-000907：原题、固定版本与贡献范围审阅

**当前结论：证据不足（待本轮隔离执行结束）。** 静态审阅确认所选源码包含原题两个问题的无额外假设终点；不能把源码阅读或以前的成功运行替代本轮实际检查。

| 必答判断 | 当前结论 | 决定性材料 |
| --- | --- | --- |
| 证明对象是否就是指定原题？ | 是，静态语义对应确认 | APSSV §4.1 两个问题；`JSP000907.jsp_000907`；本轮五个独立桥梁 |
| 指定 commit 是否实际验证通过？ | 未完成本轮验证 | 应检查 `555ce4f13bf7e8e8557020728f7f97ad3d1f51e0` 的全部 40 项目标 |
| 是否完整解决原题？ | 源码覆盖完整；最终结论待机器证据 | 第一问肯定、第二问完整否定，未把旧研究笔记的未形式化断言当假设 |
| 是否满足本轮 Lean 完整性要求？ | 暂无法确认 | 必须等待干净构建、公理、内核重放、独立导出检查及负控制全部完成 |

## 输入与原题

- 原 PR：[696](https://github.com/TheJustinSunPrize/awards/pull/696)；claim：[1588](https://github.com/TheJustinSunPrize/awards/issues/1588)。快照 base `ff33abd13163e789790eb1014e55f57c05f94432`，head `1b879d7019554bf75253c89b81bfb163a1cc777e`；分支 `jsp-000907-four-chord-note`。
- PR 文件快照只有一个题库文件的 Lean proof / Attribution basis 修改；原题描述与 `Current status` / `Eligible to claim` 没有变。
- 唯一提交的证明版本：仓库 `ketianzhang1-lang/jsp-000301-lean`，分支 `jsp-000907-complete-kz`，commit `555ce4f13bf7e8e8557020728f7f97ad3d1f51e0`，子目录 `projects/jsp-000907`。题库中的 `108f6b...` 为文档版本、`900806...` 为贡献审计，不是另一个待验 Lean 版本。
- 原始问题：[Erdős 1091](https://www.erdosproblems.com/1091)，本次直接访问返回 403。独立取得的数学原始来源是 [APSSV, arXiv:2604.06609v1, §4.1–4.5](https://arxiv.org/html/2604.06609v1#S4)，其中 §4.1 同时陈述 Voss 的肯定结果和无界加强问题。没有用搜索摘要替代原文。题库同时给出 Voss 1982 论文 DOI `10.1016/0095-8956(82)90004-1`。

原题要求任意有限四色且无 K4 的图有带至少两条弦的奇简单圈；另问是否存在趋于无穷的阈值函数，使所有至多 r 点子图可三染色的四色图必有达到该阈值的奇圈。已发表反例使用任意大图、每个圈的弦数统一不超过十。

## 覆盖矩阵

| 原题义务 | 源码与桥梁 | 对应关系与边界 |
| --- | --- | --- |
| 有限简单无向图与染色数恰为四 | `SimpleGraph V`, `[Fintype V]`, Mathlib `chromaticNumber = (4 : ENat)` | 肯定终点允许任意有限顶点类型；完整成对终点用每个 `Fin n`，不限制 n |
| K4 禁用与奇简单圈 | `CliqueFree 4`, `p.IsCycle`, `Odd p.length`；`Verify907.affirmative_literal` | 不把闭游走当简单圈；K4-free 假设正是第一问条件 |
| 弦的真实定义与不重复计数 | Mathlib `Walk.IsChord`；`Verify907.literalChordCount`, `chord_count_formula` | 过滤 `G.edgeFinset : Finset (Sym2 V)`；边的两端在圈支持内、边不在圈边表里，Sym2 消去方向重复。已读取固定 Mathlib 的 Chord.lean 实现 |
| 包括删边的所有小子图 | `smallSubgraphs_iff_induced` 双向证明；`Verify907.counterexample_literal` | `∀ H : G.Subgraph, H.verts.ncard ≤ r → H.coe.Colorable 3`；不是只检查选定诱导子图 |
| 每个自然 r 的反例 | `explicit_counterexample` | 选 m=floor(r/20)，r<n≤r+31；r=0 同样有合法非空图。上游证明 m=0 亦成立，虽论文展示以 m≥1 记述 |
| 实阈值、无单调性限制 | `realGuarantee_le_ten`, `no_diverging_realGuarantee`；两条 literal 桥梁 | 任意 f:Nat→Real，有保证即每个 r 有 f(r)≤10，因此不能趋于无穷；比整数阈值版本更强 |
| 两问一起覆盖 | `jsp_000907`, `complete_package` | Voss 肯定证明不以未证的结构分类接口为前提；调用实际完成的 maximal-ear/coloring 链 |
| 额外声明的全部贡献 | 29 个本地公共定理 + 六个原上游审计终点 | 任意底图的强制染色构造、任意奇轮大小、九圈四条弦等全部列入本轮清单；未声称这是独立新完整解 |

上游根文件同时包含带显式假设的可选接口 `affirmative_of_vossDegreeBound` 等；最终肯定定理并不通过假定这些接口完成。静态追踪为有限临界子图 → 最短奇圈 → maximal-ear 分类 → 实际染色扩展；本轮将检查最终传递闭包。第二问调用已证的 APSSV 有限构造，不依赖本人的旧奇轮笔记中未形式化的全圈四弦上界或临界性。

## 执行清单和可信边界

`907-targets.json` 共 **40 项**，包含原 verifier 的 **35 项**（29 本地 + 六上游）和 **五项新桥梁**。清单每项均对应至少一条原题或附加声明要求。38 个上游模块由 `UPSTREAM.json` 固定不可变 URL、Git blob、原始 SHA256、全部兼容修改和修改后 SHA256；六个上游终点通过已跟踪且已配置的 `AuditComplete` 入口检查，真实定义源和 port SHA256 分开记录，不冒充已跟踪文件。

原 verifier 无 `--resume` 重新编译 **43 个模块**，含全部 38 个上游模块、四个本地模块和 `AuditComplete`；执行标准公理检查、五组内核重放、九个实际依赖 revision 检查、`1=0` 负控制和原笔记哈希核验。框架另做每个目标的 `#check/#print/#print axioms`、独立桥梁、导出闭包与 NaNoda 硬白名单复核。Lean 4.34.0；Mathlib `5ed2965256430c3649e86755f9576b54eca72435`；固定 exporter 和 NaNoda 版本由 config 记录。exporter 使用已披露的 4.34 兼容重建。标准经典基础 `propext`, `Classical.choice`, `Quot.sound` 与证明缺口区分；不允许 sorryAx、自定义替代假设或 native/compiler trust 公理。

静态扫描本地模块未发现 sorry/admit/axiom/native_decide/skipKernelTC；此扫描不能替代传递公理审计。实际执行只能由隔离非 root Docker、断网检查阶段完成；审阅者没有在本地运行 Lean/Lake。

## 归属、许可与最新模板修订

Voss 保留肯定结果数学归属。APSSV 论文说明证明来自 OpenAI 内部模型，人类作者消化、改写并对临界性论证提出改进；应同时保留这些披露，不把人名作者列表变成独立人类发现声明。原 Lean 来源 `plby/lean-proofs@8822f7ddef30fadbd92e1c6ab4ed897af356af5e` 根文件署 OpenAI Codex，Brooks 发展署 Brian Rabern / Opus 5；其他源头署名亦保留。本地四模块署 ketianzhang1-lang，明确 ChatGPT/Codex 辅助。Apache-2.0 文件许可和上游通知保留；仓库根历史 MIT 不能替换文件级许可。

本轮 replacement 补齐最新模板的原题来源、固定 formal statement、提交 JSON、solver 先审查/候选注册前提、自查四项结论位置、原 PR 打开前自查历史限制及 claim 的 merged PR 项；保留旧贡献范围和相关申报冲突。1399、274 仍 open，1057、1019 closed（已读取当前正文；历史撤回理由沿原声明披露）。无已完成身份核验、首提或授奖声明。

PR 原打开时间不可通过本轮补做自查追溯改写；相应框保持未勾选。claim 必须等待 PR 合并，不能把待处理 PR 填成已经合并。solver 注册、数学审核、身份/归属与奖金资格仍由主办方决定。

## 首轮真实执行与审计入口修复

首轮 run `35484654492` / job `106008713532` 的原样完整 verifier 和独立桥梁严格预编译均通过；官方逐目标审计的 **35 个原定理全部通过**。只有五个审计桥梁在 `lake build +JSP000907.VerificationBridge` 阶段报告 `unknown module`。原 Lake 配置的 roots 包含 `JSP000907Complete`，并不包含名为 `JSP000907` 的根模块。

本轮将**同字节桥梁**移到 `JSP000907Complete/VerificationBridge.lean`，对应模块 `JSP000907Complete.VerificationBridge`，更新五个清单入口。已读固定 Lean 4.34 的 Lake `LeanLibConfig.isBuildableModule` 实现，确认已配置 roots 的子模块属于原生可构建模块。没有改原证明、lakefile、官方脚本或目标数学内容，也不需 adapter。修复后的完整重跑仍是最终通过结论的必要条件；失败原始证据保留。
