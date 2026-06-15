# Codex Boolean Analysis Project Summary

本文档总结当前 Lean 项目用于形式化 Ryan O'Donnell, *Analysis of Boolean Functions* 的进展、配置和下一步计划。

## 1. 项目目标

本项目的核心目标是逐步用 Lean 4 / mathlib 形式化 *Analysis of Boolean Functions* 的基础章节：

- 第一章：Boolean cube、Fourier expansion、characters、Parseval、Plancherel、BLR test。
- 第二章：basic Boolean functions、influence、Poincare inequality、edge-isoperimetric theorem、noise stability。
- 长期目标：把教材中的 definitions、facts、propositions、theorems 尽量升级为 Lean 中完整证明过的 theorem。

当前工作目录：

```text
C:\Users\phyao\Documents\Lean start
```

Lean 项目根目录就在该目录下，`lakefile.toml` 也在这里。运行 `lake build` 时必须在这个根目录运行。

## 2. 项目结构

主要入口文件：

```text
BooleanFunctions.lean
InformationTheory.lean
lakefile.toml
lean-toolchain
```

主要目录：

```text
BooleanFunctions/
InformationTheory/
TQI/
.lake/packages/
```

`BooleanFunctions/` 是本项目关于 Boolean functions 的主目录。当前重要文件包括：

```text
BooleanFunctions/Fourierexpansion.lean
BooleanFunctions/BasicFunctions.lean
BooleanFunctions/Influence.lean
BooleanFunctions/Thm Inf Core.lean
BooleanFunctions/Thm Inf.lean
BooleanFunctions/Poincare.lean
BooleanFunctions/Thm 2.33.lean
BooleanFunctions/Thm 2.39.lean
BooleanFunctions/majority.lean
BooleanFunctions/sorry.lean
BooleanFunctions/BLR.lean
BooleanFunctions/Parseval.lean
BooleanFunctions/Plancherel.lean
BooleanFunctions/noise stability.lean
BooleanFunctions/thm noise stability.lean
```

章节文件：

```text
BooleanFunctions/Thm sec 1_1.lean
BooleanFunctions/Thm sec 1_3.lean
BooleanFunctions/Thm sec 1_4.lean
BooleanFunctions/Thm sec 1_5.lean
```

`InformationTheory/` 是另一个 Lean library，目前包括 entropy、divergence、channels、AEP、coding 等相关文件。它由同一个 Lake 项目管理。

## 3. Lean / Lake 依赖配置

Lean 版本由 `lean-toolchain` 指定：

```text
leanprover/lean4:v4.30.0
```

`lakefile.toml` 当前核心配置：

```toml
name = "BooleanFunctions"
version = "0.1.0"
keywords = ["math", "formalization"]
defaultTargets = ["BooleanFunctions", "TQI", "InformationTheory"]

[leanOptions]
pp.unicode.fun = true
relaxedAutoImplicit = false
maxSynthPendingDepth = 3

[[require]]
name = "mathlib"
path = ".lake/packages/mathlib"

[[require]]
name = "Physlib"
path = ".lake/packages/PhysLean"

[[lean_lib]]
name = "BooleanFunctions"

[[lean_lib]]
name = "TQI"

[[lean_lib]]
name = "InformationTheory"
```

几个注意点：

- `mathlib` 是本地 path dependency，路径为 `.lake/packages/mathlib`。
- `Physlib` 也是本地 path dependency，路径为 `.lake/packages/PhysLean`。
- 因为依赖走本地路径，网络不稳定时也可以继续构建，只要本地依赖完整。
- 运行 `lake build` 必须在 `C:\Users\phyao\Documents\Lean start`，不能在 `C:\Users\phyao` 或 `BooleanFunctions/` 子目录下运行。
- 单文件检查可用：

```powershell
lake env lean "BooleanFunctions/Thm 2.39.lean"
```

- library 构建可用：

```powershell
lake build BooleanFunctions
```

最近一次 `lake build BooleanFunctions` 成功；警告只来自 `BooleanFunctions/sorry.lean` 中集中保留的 `sorry`。

## 4. 最近遇到的问题

### 4.1 Lake 工作目录问题

曾经在 `C:\Users\phyao` 或 `BooleanFunctions/` 下运行 `lake build`，报错：

```text
no configuration file with a supported extension
```

原因是 Lake 找不到 `lakefile.toml`。解决方式是切换到项目根目录：

```powershell
cd "C:\Users\phyao\Documents\Lean start"
lake build BooleanFunctions
```

### 4.2 mathlib 下载问题

最初 VS Code / Lake 自动 clone mathlib 时遇到网络错误：

```text
fatal: unable to access 'https://github.com/leanprover-community/mathlib4/':
Recv failure: Connection was reset
```

后来改为把 mathlib 放到本地 `.lake/packages/mathlib`，并在 `lakefile.toml` 里用 path dependency。

### 4.3 Windows 路径和文件名

项目路径和部分 Lean 文件名包含空格，例如：

```text
Lean start
Thm 2.39.lean
noise stability.lean
```

PowerShell 命令中需要加引号。Lean import 中需要使用 guillemet syntax，例如：

```lean
import BooleanFunctions.«Thm 2.39»
```

### 4.4 `statement` 与 theorem 的升级

之前有一些教材命题先用 `Statement...` 表达为命题壳，再逐步升级为 theorem。这样做的好处是可以先固定数学接口，再补证明。

目前已经升级的重要例子：

- `Statement2_33` 已在 `Thm 2.33.lean` 中升级为 `theorem_2_33`。
- `Statement2_39` 已在 `Thm 2.39.lean` 中升级为完整证明的 `theorem_2_39`。

仍然存在的 statement 主要集中在 section 2.4 的 noise stability 相关文件里。

### 4.5 Theorem 2.39 的关键技术问题

Theorem 2.39 的证明不能只直接对两个 slice 的 `Pr[f = -1]` 套归纳假设，因为某个 slice 的 `Pr[f = -1]` 可能大于 `1/2`。

解决方案是引入：

```lean
minorityProbability f =
  min (Pr[f = -1]) (Pr[f = 1])
```

并证明：

- 取负 Boolean function 不改变 total influence。
- 取负 Boolean function 交换 `Pr[f = -1]` 和 `Pr[f = 1]`。
- 归纳假设可应用到任意 slice 的 minority probability。
- 实数端补充 complement 比较和 midpoint inequality。

这样才能完成按最后一个坐标 slicing 的归纳证明。

## 5. 已做过的主要修改

### 5.1 基础 cube / Fourier 文件

- 将早期 `Cube.lean` 改名为 `Fourierexpansion.lean`。
- 保留两个 cube 表示：
  - `SignCube n` 表示 `{-1, 1}^n`
  - `Cube01 n` 表示 `{0, 1}^n`
- 删除一批同义别名，避免初学 Lean 时概念过多。
- 定义了 expectation、inner product、Fourier characters、Fourier coefficients 等基础对象。

### 5.2 第一章

已经拆分并形式化了多个第一章内容：

- Section 1.1: cube / characters / Theorem 1.1
- Section 1.3: Fourier expansion, Theorem 1.5, Fact 1.6, Fact 1.7
- Section 1.4: basic Fourier formulas
- Parseval 单独放入 `Parseval.lean`
- Plancherel 单独放入 `Plancherel.lean`
- BLR test 放入 `BLR.lean`

### 5.3 第二章 influence 相关

- `BasicFunctions.lean`：形式化 section 2.1 的基础函数。
- `Influence.lean` / `Thm Inf Core.lean` / `Thm Inf.lean`：整理 section 2.2 和 2.3 的 definitions、facts、propositions、theorems。
- `Poincare.lean`：形式化 Poincare inequality。
- `Thm 2.33.lean`：单独整理 Theorem 2.33，包含 uniqueness 相关证明。
- `majority.lean`：整理 exercise 2.22 majority influence 的形式化蓝图和部分证明。
- `sorry.lean`：集中收集暂时允许的外部/复杂输入，例如 Stirling formula 和 majority asymptotics 相关结论。

### 5.4 Theorem 2.39

`BooleanFunctions/Thm 2.39.lean` 已完成完整形式化。

新增内容包括：

- `negateSignFunction`
- `minorityProbability`
- 取负后概率交换：
  - `signValueProbability_negate_negOne`
  - `signValueProbability_negate_posOne`
- 取负不改变 influence / total influence：
  - `influence_neg`
  - `totalInfluence_neg`
  - `totalInfluence_negateSignFunction`
- minority probability 相关引理：
  - 非负
  - 不超过 `1/2`
  - 在 `Pr[f=-1] <= 1/2` 或 `Pr[f=1] <= 1/2` 时化简
- edge-isoperimetric lower bound 的实数引理：
  - midpoint inequality
  - complement comparison
  - probability-to-minority comparison
- 最终定理：

```lean
theorem theorem_2_39 : ∀ n : Nat, Statement2_39 n
```

该文件没有 `sorry` 或 `axiom`。

### 5.5 Noise stability

已经开始 section 2.4：

- `noise stability.lean`：definitions
- `thm noise stability.lean`：除 Theorem 2.45 外的部分 facts / propositions / theorems / statements

注意：当前这两个文件在工作区中仍显示为未跟踪文件，需要决定是否纳入下一次 commit。

## 6. 当前工作区状态

最近已经提交：

```text
ba822b4 update
```

该 commit 完成了 `Thm 2.39.lean` 的完整形式化。

当前仍有未提交改动：

```text
BooleanFunctions.lean
InformationTheory.lean
BooleanFunctions/noise stability.lean
BooleanFunctions/thm noise stability.lean
InformationTheory/OptimalCode.lean
```

其中：

- `BooleanFunctions.lean` 似乎已经加入了 noise stability 相关 import。
- `InformationTheory.lean` 似乎已经加入了 `OptimalCode` 相关 import。
- 上述新文件还没有被 git 跟踪。

提交新工作前需要先决定这些文件是否属于同一批改动。

## 7. 当前剩余 `sorry`

当前 `BooleanFunctions/sorry.lean` 中还有集中保留的 `sorry`，主要用于 majority / Stirling / asymptotic 相关结论。

原则上：

- 可以暂时把复杂实分析或渐近估计集中放在 `sorry.lean`。
- 普通教材命题应逐步从 `Statement...` 升级为 theorem。
- 每次完成一个 theorem 文件后，应检查该文件本身没有 `sorry` 和 `axiom`。

## 8. 下一步建议

### 8.1 清理并提交当前未提交文件

优先确认这些文件是否都应纳入版本控制：

```text
BooleanFunctions.lean
InformationTheory.lean
BooleanFunctions/noise stability.lean
BooleanFunctions/thm noise stability.lean
InformationTheory/OptimalCode.lean
```

如果它们属于 noise stability / information theory 的新进展，应单独检查、build、commit。

### 8.2 继续 section 2.4 noise stability

下一批工作建议：

- 检查 `noise stability.lean` 中 definitions 是否命名稳定。
- 检查 `thm noise stability.lean` 中还有哪些 `Statement...`。
- 优先升级容易证明的 propositions/facts。
- Theorem 2.45 暂时跳过，保持单独计划。

### 8.3 处理 `sorry.lean`

建议分两类处理：

- Stirling formula / asymptotics：评估是否引用 mathlib 现成 Stirling 定理，还是继续作为外部输入。
- majority influence：逐步把组合恒等式、`Nat.choose`、奇数子序列渐近拆成小 lemma。

### 8.4 把稳定公共引理迁移到基础文件

现在一些通用 lemma 还在 theorem 文件里，例如：

- 取负函数不改变 total influence
- minority probability
- 概率 complement 关系

如果后续章节也需要这些工具，可以考虑从 `Thm 2.39.lean` 移到更基础的文件，例如 `Influence.lean` 或 `Thm Inf Core.lean`。迁移时要小心避免 import cycle。

### 8.5 建立固定验证流程

建议每次完成一个阶段运行：

```powershell
lake env lean "BooleanFunctions/目标文件.lean"
lake build BooleanFunctions
rg -n "\bsorry\b|\baxiom\b" BooleanFunctions
```

如果只允许 `BooleanFunctions/sorry.lean` 中有 `sorry`，则用搜索结果确认其他文件没有新增 `sorry`。

## 9. 给以后 Codex 的操作提醒

- 不要在错误目录运行 `lake build`。
- 不要随意 revert 用户已有改动。
- 提交时只 stage 当前任务相关文件。
- 文件名有空格时，PowerShell 命令要加引号。
- Lean import 文件名有空格时使用 `«...»`。
- Theorem 2.39 已经完整证明，不要再把它退回 statement。
- 当前最值得继续推进的是 section 2.4 noise stability 和 `sorry.lean` 中的 majority/Stirling 输入。
