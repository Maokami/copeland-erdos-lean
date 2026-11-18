# Mathlib 의존성 조사

조사일: 2026-11-17. **소스 확인 결과이며 `#check` 또는 `lake build` 결과가 아니다.**

후속 상태: 이 문서는 최초 조사의 기록이다. 2026-11-18에 유한 모멘트 도구와
최종 정규성까지 구현·빌드했으며, 현재 상태는 [최종 검증](verification-complete.md)을 따른다.

- 소스: `/Users/jaeho/projects/playground/kuratowski/.lake/packages/mathlib`
- SHA: `56a005855ea17e0b0958f73ec801ae140b0a1679`
- Lean: `leanprover/lean4:v4.35.0`
- 조사: `gpt-6.1-sol` / `xhigh` 작업자. 메인 Astra가 핵심 소수 하한과 실수 전개 소스를 추가 확인했다.
- 소스의 수정·의존성 다운로드·무거운 빌드는 수행하지 않았다.

## 1. 소수 개수: 새 소수정리 프로젝트가 필요하지 않다

[Chebyshev.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/Chebyshev.lean#L806)
에 다음 선언이 있다. 표기는 읽기 편하게 실수 coercion을 명시했다.

```lean
Chebyshev.pi_ge (n : ℕ) :
  (n * Real.log 2 - Real.log (n + 1)) / Real.log n ≤
    (Nat.primeCounting n : ℝ)

Chebyshev.pi_ge' {x : ℝ} (hx : 1 < x) :
  ((x - 1) * Real.log 2 - Real.log (x + 2)) / Real.log x ≤
    (Nat.primeCounting ⌊x⌋₊ : ℝ)
```

`pi_ge` 자체는 `n=0,1`도 포함하지만, 로그로 나누는 해석에는 `n>1`을 확보해야 한다.
충분히 큰 `n`에서 `c n/log n ≤ π(n)`을 얻는 작은 극한 보조정리는 새로 작성한다.

관련 API:

| 파일 | 선언 | 역할 |
|---|---|---|
| `Analysis/SpecialFunctions/Log/Basic.lean:450` | `Real.isLittleO_log_id_atTop` | 로그가 일차식보다 느리게 성장 |
| `Analysis/SpecialFunctions/Pow/Asymptotics.lean:355` | `Real.isLittleO_log_rpow_atTop` | 양의 거듭제곱과 로그 비교 |
| `Analysis/SpecialFunctions/Pow/Real.lean:885` | `Real.log_le_rpow_div` | 명시적 로그 상계 |
| `NumberTheory/PrimeCounting.lean:261` | `Nat.primesLE_card_eq_primeCounting` | `≤ n`인 소수의 개수 |
| 같은 파일 `:254` | `Nat.primesBelow_card_eq_primeCounting'` | `< n`인 소수의 개수 |
| `NumberTheory/Bertrand.lean:225` | `Nat.exists_prime_lt_and_le_two_mul` | 다음 소수 `≤ 2n`의 근거 |

Bertrand의 계약은 `n ≠ 0 → ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2*n`이다.
연속된 소수의 경우로 옮기는 wrapper는 필요하다.

`Chebyshev.pi_le_log4_mul_div`라는 명시적 상계도 있지만 현재 종이 증명은 필요로 하지 않는다.
평균 소수 블록 길이가 무한대로 간다는 사실로 경계 밀도를 제어한다.
Mathlib 내부 하한 증명은 `choose_dvd_lcmUpto`, `two_pow_le_mul_lcmUpto`, `psi_ge`를 거친다.
이를 프로젝트에서 다시 증명할 이유는 없다.

## 2. 유한 평균과 4차 모멘트

현재 조사 범위에서는 독립 중심화 변수 합의 원하는 4차 모멘트 식을 바로 주는 선언을 찾지 못했다.
다음 유한 평균 API를 재사용하여 2차·4차 모멘트의 귀납식을 구현하는 경로를 추천한다.

`Mathlib/Algebra/BigOperators/Expect.lean`:

- `Finset.expect` (`:60`)
- `Finset.expect_sum_comm`, `expect_add_distrib`, `expect_sub_distrib`
- `Finset.expect_product`, `expect_product'` (`:260`, `:267`)
- `Finset.expect_mul_expect` (`:334`)
- `Finset.expect_eq_sum_div_card`, `Fintype.expect_eq_sum_div_card` (`:367`, `:371`)

순서 부등식은 `Algebra/Order/BigOperators/Expect.lean`의
`Finset.expect_le_expect`, `expect_le`, `expect_nonneg`가 출발점이다.
`Fintype.sum_pow` (`Algebra/BigOperators/Ring/Finset.lean:299`)로 4중 합을 전개하는
대안도 있지만, 곱 공간을 마지막 좌표와 나누어 귀납하는 편이 인덱스 분류를 줄인다.

### 대안: 이미 있는 지수 꼬리 상계

`Probability/Moments/SubGaussian.lean`에는
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`와
`ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`이 있다.
이를 쓰면 더 강한 예외 집합 상계를 얻을 수 있지만 유한 균등 측도, 블록 독립성,
중심화, 실수 측도에서 cardinality로의 연결을 구현해야 한다.

먼저 유한 평균 경로를 사용한다. 실제 구현 부담이 더 크다는 근거가 생기면 이 대안을 비교한다.
원 논문의 일반 정리를 추가 목표로 삼는 경우에는 지수 꼬리 경로의 가치가 커진다.

## 3. 자리 숫자, 단어, 이어 붙이기

| 파일 | 재사용 선언 | 주의 |
|---|---|---|
| `Data/Nat/Digits/Defs.lean` | `Nat.digits_lt_base`, `Nat.ofDigits_digits` | 숫자 목록은 **little endian** |
| 같은 파일 `:166` | `Nat.ofDigits_append` | 오른쪽 목록에 자리 가중치가 붙음 |
| `Data/Nat/Digits/Lemmas.lean:52` | `Nat.length_digits` | `1<b`, `n≠0` 필요 |
| 같은 파일 `:65`, `:73` | `Nat.digits_length_le_iff`, `Nat.lt_digits_length_iff` | 길이와 거듭제곱의 비교 |
| 같은 파일 `:400–444` | `Nat.fixedLengthDigits`, `mem_fixedLengthDigits_iff`, `card_fixedLengthDigits` | 선행/후행 0을 허용하는 고정 길이 공간 |
| 같은 파일 | `Nat.bijOn_ofDigits`, `Nat.bijOn_digitsAppend` | 단어와 정수 범위의 일대일 대응 |
| `Data/Fintype/BigOperators.lean:138` | `Fintype.card_pi_const` | `Fin ℓ → Fin b`의 크기 `b^ℓ` |
| `Analysis/SpecialFunctions/Log/Base.lean:401` | `Real.natFloor_logb_natCast` | 자연수 로그와 실수 로그 연결 |

`Nat.digits b 0=[]`이다. 프로젝트의 소수 블록은 모두 양수이므로 이 경우는 주 정리에 나타나지 않는다.
Python 검사의 `digits(0)=(0,)`는 별도의 통상적 표현이며 Lean 정의와 일치한다고 주장하지 않는다.

Lean core의 `List.length_flatten`, `List.flatten_append`, `List.countP_append`,
`List.countP_flatten`은 재사용 가능하다. 그러나 `countP`는 개별 원소를 세며
겹치는 길이-k 블록을 직접 세는 API가 아니다. 블록 출현 정의와 경계 부등식은 새로 작성해야 한다.

`Stream' α`는 `ℕ → α`이고 유한 prefix 관련 API가 있다.
가변 길이 양의 블록들의 무한 이어 붙이기는 누적 길이로 직접 구성하는 계획이다.

## 4. 실제 실수로의 연결

[Analysis/Real/OfDigits.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Real/OfDigits.lean)
에 다음이 있다.

- `Real.ofDigits (d : ℕ → Fin b) : ℝ`
- `Real.summable_ofDigitsTerm`, `Real.ofDigits_nonneg`, `Real.ofDigits_le_one`
- `Real.ofDigits_eq_sum_add_ofDigits`, `Real.abs_ofDigits_sub_ofDigits_le`
- `Real.digits`, `Real.ofDigits_digits`

`Real.ofDigits_digits`의 방향은 `ofDigits (digits x b) = x`다.
임의 숫자열에 대한 역방향을 그대로 적용할 수 없다. `0.999…=1`도 API에서 허용한다.
정규 숫자열은 결국 전부 `b−1`인 꼬리를 갖지 않음을 증명하고, 표준 자리 숫자와의
일치를 따로 증명해야 한다. 마지막 정리에서 이 연결을 빼지 않는다.

## 5. 아직 새로 필요한 것

조사한 정확한 revision에서 Copeland–Erdős, Champernowne, 숫자 블록 빈도에 기반한
정규수 정의/정리 및 원하는 블록 출현 계수 API는 찾지 못했다. 이는 전 세계 모든 Lean
저장소에 관련 구현이 없다는 주장도, 최초 형식화를 보장하는 조사도 아니다.

새 작업은 (1) 블록 계수와 무한 이어 붙이기, (2) 유한 평균의 4차 모멘트 및 나쁜 단어 상계,
(3) 길이별 합산과 소수 자릿수 질량의 극한, (4) 임의 접두사 정규성,
(5) `Real.digits`와의 연결이다. 모든 선언은 실제 구현 단계에서 컴파일로 재확인해야 한다.
