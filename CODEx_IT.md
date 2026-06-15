# CODEx_IT: InformationTheory Project Notes

本文档总结当前 `InformationTheory` Lean 项目的结构、依赖、近期问题、已经完成的修改，以及下一步建议。

## 1. 项目结构

仓库根目录是一个 Lake workspace，目前项目名仍然是 `BooleanFunctions`，但 `lakefile.toml` 中已经注册了三个 Lean library target：

```toml
defaultTargets = ["BooleanFunctions", "TQI", "InformationTheory"]

[[lean_lib]]
name = "BooleanFunctions"

[[lean_lib]]
name = "TQI"

[[lean_lib]]
name = "InformationTheory"
```

`InformationTheory.lean` 是信息论项目的总入口，负责 import 各章节文件。当前主要目录如下：

```text
InformationTheory.lean
InformationTheory/
  Basic.lean                 有限 alphabet、实值 PMF、JointPMF、Channel 等基础对象
  Probability.lean           marginal、product mass、channel-induced joint mass
  Entropy.lean               entropy、joint entropy、conditional entropy、mutual information、relative entropy 定义
  thm_entropy.lean           Section 2.1 entropy 基础定理
  thm_jointentropy.lean      Section 2.2 joint/conditional entropy 相关定理
  Thm_chainrule.lean         Section 2.5 chain rules
  Jensen.lean                Section 2.6 Jensen inequality
  logsum.lean                Section 2.7 log-sum inequality
  Inequalities.lean          信息不等式、Gibbs、相对熵非负、entropy concavity、mutual information convex/concave 等
  data_processing_ineq.lean  Section 2.8 data-processing inequality 相关 statement/proof
  Fano.lean                  Section 2.10 Fano 相关 lemma/corollary/theorem
  AEP.lean                   Chapter 3 convergence、typical set 等定义
  thm_AEP.lean               Chapter 3 AEP/typicality 相关 theorem
  datacompression.lean       Section 5.1 source code、extension、UD、prefix code、expected length
  Kraft.lean                 Section 5.2 Kraft/McMillan inequalities and converses
  OptimalCode.lean           Section 5.3 Theorem 5.3.1
  SourceCoding.lean          后续 source coding roadmap
  ChannelCoding.lean         后续 channel coding roadmap
  Blueprint.lean             项目路线图
  README.md                  项目概览
  elements of information theory_Unknown Author.pdf
```

整体风格是：定义放在章节主文件中，证明放在 `thm_*` 或章节 theorem 文件中；后面源编码章节目前按 section 单独建文件。

## 2. Lean/Lake 依赖配置

Lean 版本由 `lean-toolchain` 固定：

```text
leanprover/lean4:v4.30.0
```

Lake 依赖在 `lakefile.toml` 中使用本地 path：

```toml
[[require]]
name = "mathlib"
path = ".lake/packages/mathlib"

[[require]]
name = "Physlib"
path = ".lake/packages/PhysLean"
```

这意味着当前配置依赖本机 `.lake/packages/mathlib` 和 `.lake/packages/PhysLean` 已经存在；它不是从 Git URL 自动拉取的配置。如果在新机器或新 clone 上复现，需要确保这两个目录可用，或者把 `lakefile.toml` 改成远端依赖形式后再 `lake update`。

常用检查命令：

```powershell
lake build InformationTheory
lake env lean InformationTheory\OptimalCode.lean
rg -n "sorry|axiom|admit" InformationTheory InformationTheory.lean
```

最近一次完整验证：

```text
lake build InformationTheory
Build completed successfully (2345 jobs).
```

并且 `InformationTheory` 目录和 `InformationTheory.lean` 中没有发现 `sorry`、`axiom`、`admit`。

## 3. 最近遇到的问题

1. Mathlib 已经有一些重叠内容，包括一般测度论版本的 KL divergence、convex/Jensen 工具、log 相关定理，以及 coding 里的 Kraft-McMillan theorem。当前项目保留教材风格的有限、实值 PMF 层，但尽量复用 mathlib 的分析和 coding 定理，避免重复造底层工具。

2. 教材公式默认处理 `0 log 0 = 0`，而 Lean 里的实函数是 total function。项目中相对熵、互信息、entropy term 都显式采用 `if p = 0 then 0 else ...` 的零质量约定；很多 theorem 因此需要 support 条件，例如 `p a ≠ 0 -> q a ≠ 0`。

3. Theorem 5.2.2 的 statement 涉及 countably infinite set。有限版本可以直接接 mathlib 的 finite Kraft-McMillan；countable 版本需要通过 `Nat` source、partial sums、summability/tsum、monotone length construction 等方式处理，不能简单把 finite proof 原样套上。

4. Section 5.3 Theorem 5.3.1 需要把教材的
   `L - H_D(X) = D(p || r) + log_D(1/c)`
   翻译成现有 Lean 库中可证明的形式。最终做法是用 base-2 log-sum inequality 先证明
   `H_2(P) <= log_2(D) * L`，再通过 change-of-base 得到
   `H_D(P) <= L`。

5. Windows PowerShell 默认输出编码有时会把 Lean 文件里的 Unicode 显示成乱码，但 Lean 编译本身没有问题。读取 PDF 文本时也需要注意 `PYTHONIOENCODING=utf-8`。

## 4. 已做过哪些修改

已经搭建并持续扩展了 `InformationTheory` 这条独立 formalization 线：

1. 建立有限实值 PMF 基础层，包括 `PMF`、`JointPMF`、`Channel`、marginal/product/channel-induced mass。

2. 形式化 Chapter 2 的核心对象和定理：
   entropy、joint entropy、conditional entropy、mutual information、relative entropy、chain rules、Jensen、log-sum、Gibbs/information inequality、data processing、Fano。

3. 形式化 Chapter 3 的 AEP/typicality 基础定义和若干 theorem。

4. 形式化 Chapter 5.1 的 source code 相关定义：
   `SourceCode`、codeword length、expected length、extension、nonsingular、uniquely decodable、prefix/instantaneous code。

5. 形式化 Chapter 5.2 的 Kraft 和 McMillan 相关 theorem：
   `theorem_5_2_1_kraft_inequality`
   `theorem_5_2_1_kraft_converse`
   `theorem_5_2_2_mcmillan_inequality_finite`
   `theorem_5_2_2_mcmillan_inequality`
   `theorem_5_2_2_mcmillan_converse_finite`
   `theorem_5_2_2_mcmillan_converse`

6. 新增 `InformationTheory/OptimalCode.lean`，形式化 Section 5.3 Theorem 5.3.1：
   `theorem_5_3_1_optimalCode_lower_bound`
   `theorem_5_3_1_optimalCode_equality_iff`
   `theorem_5_3_1_optimalCode`

   其中完整 theorem statement 包含：

   ```lean
   entropyWithBase (D : Real) P <= C.expectedLength P
   ```

   以及 equality characterization：

   ```lean
   C.expectedLength P = entropyWithBase (D : Real) P ↔
     forall x, P.prob x = (1 / (D : Real)) ^ C.length x
   ```

7. 已将 `InformationTheory.lean` 更新为 import `InformationTheory.OptimalCode`。

## 5. 下一步要做什么

建议下一步从 Chapter 5 source coding 继续推进：

1. 给 Section 5.3 增加教材术语层的定义，例如 optimal code、optimal expected length、length assignment optimality。当前 theorem 已经证明任意 instantaneous code 的 lower bound，但还没有把 “optimal code” 本身定义成 minimizer。

2. 继续形式化 Section 5.4 关于 optimal code length bounds 的 theorem，通常会用到 `ceil (-log_D p_i)`、Kraft converse、expected length 上界和下界。

3. 把 Chapter 5 中 finite source 和 countable source 的边界统一整理清楚。有限 alphabet 可以继续使用 `Fintype alpha`；countable infinite 的 theorem 应明确使用 `Nat` 或后续抽象的 countable index type。

4. 给已有 theorem 加更多教材同名 alias 或 theorem 注释，方便按书中编号查找。

5. 逐步建立与 mathlib 概率/测度论对象的 bridge theorem，但不要过早替换当前有限实值层；现在的有限层更贴近教材前几章，也更利于快速推进。

6. 增加 CI 或至少固定一个常用验证命令：每次提交前跑 `lake build InformationTheory` 和 `rg -n "sorry|axiom|admit" InformationTheory InformationTheory.lean`。
