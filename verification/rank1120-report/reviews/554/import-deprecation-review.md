# JSP-000554：四条 import 弃用警告的精确归类

**结论：四条真实警告均来自固定 Mathlib 的旧 import 路径；需要完整披露，但不是目标证明失败，也不能称为“零警告构建”。** 原证明 commit `21fcf006fd68b0bead9f979b704c92032f05cba8` 没有为消除它们而修改。此判断不放行其他警告、错误、非零退出码或哈希变化。

实际证据来自 [run 35485853057 / job 106011976984](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35485853057/job/106011976984)。原 verifier 逐模块传入 `-DwarningAsError=true`，完整构建阶段实际退出 0；随后 44 个清单目标、kernel replay 和 NaNoda 均完成。不能仅凭该退出码忽略编译器日志，因此另行核对了下面四条消息及其产生路径。

| 实际定义文件 | import 行 | 弃用路径 |
|---|---:|---|
| `ErdosProblems/Erdos387/CoverBPZPrelude.lean` | 23 | `Mathlib.Data.Real.Basic` |
| `ErdosProblems/Erdos387/LocalDensity.lean` | 6 | `Mathlib.Data.Real.Basic` |
| `ErdosProblems/Erdos851/FiniteCombinatorialSieve.lean` | 6 | `Mathlib.Data.Real.Basic` |
| `ErdosProblems/Erdos851/RosserCore.lean` | 6 | `Mathlib.Data.Real.Basic` |

[精确诊断策略](inspector-source-diagnostics.json) 逐条绑定实际源码路径、行号、源码 SHA256、原始日志路径与 SHA256、完整消息及原编译参数。四份日志均只有相应 import 弃用提示，建议新路径 `Mathlib.Basic.Real.Basic`；不将它们归为 Lake 依赖 URL 拼写提示。所有原始消息保留在 raw evidence。

## 为什么 warningAsError 没有令这四条消息失败

核对的是 Lean 4.34.0 的实际源码 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`：

1. [Import.lean 的 checkDeprecatedImports](https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/Lean/Elab/Import.lean#L61) 在处理文件头时直接将 warning 加入 MessageLog。该路径没有调用常规日志入口。
2. [Log.lean 的 logAt](https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/Lean/Log.lean#L110) 才读取 warningAsError，并把常规 warning 提升为 error。文件头中的直接加入路径绕过了这一步；不是证明文件自行关闭该选项。
3. [Message.lean](https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/Lean/Message.lean#L687) 直接存储已确定的消息级别；[Language/Basic.lean 的 reportMessages 和 runAndReport](https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/Lean/Language/Basic.lean#L414) 根据最终 error 数判断失败，不再依据 warningAsError 全局提升已有的文件头 warning。

在实际 checked-source 中没有找到 `warningAsError false` 或 `deprecated_module: ignore`。上述固定源码已经由第二位审阅者独立取得并核对 SHA256；没有通过修改编译器或屏蔽日志解释此结果。

## 对证明和本次要求的影响

固定 Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435` 的 [旧模块](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Data/Real/Basic.lean) 只有模块指令、对 [新模块](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Basic/Real/Basic.lean) 的 public import，以及弃用标记。它没有添加数学声明、公理或占位证明。因此这四条消息说明文件使用兼容转发路径，而非缺失证明步骤。这个判断限于所列具体文件和哈希。

[固定官方 lean-verify](https://github.com/TheJustinSunPrize/awards/blob/38e63c424c7196f8d4ceb664c5c25f0c0529d5e2/skills/lean-verify/SKILL.md) 要求原样干净构建、确切目标与公理检查成功，并完整保留诊断；未规定一切 warning 均须先改源码消除。[报告模板](https://github.com/TheJustinSunPrize/awards/blob/38e63c424c7196f8d4ceb664c5c25f0c0529d5e2/skills/lean-verify/references/report-template.md#L63) 要求说明警告与目标及证明依赖的关系。本次据此作精确分类，保留原版本和全部日志；原始目标、独立 bridge 及标准公理限制仍须逐项成立。

若今后另行整理 import 路径，应发布新的证明版本，更新 UPSTREAM.json 中四份兼容移植的编辑记录及 port SHA256，并重新执行完整验证。不能把新版本的结果替代本次所选历史 commit 的证据；消除这四条弃用提示不是当前官方完整性要求的额外门槛。
