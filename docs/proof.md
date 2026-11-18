# 소수 이어 붙이기의 정규성: pencil-and-paper 증명

상태: **아래 소수 정규성 논증과 실제 실수 전개 연결을 Lean으로 구현·검증했다** (2026-11-18).
메인 Astra가 종이 증명·계약·소스 대응을 검토하고, 사용자 지정 Sol 작업자가 구현했다.
최종 근거는 [통합 검증](verification-complete.md), 선언 대응은 [증명 지도](proof-map.md)에 있다.
Chebyshev와 Bertrand 등 기존 Mathlib 정리의 재사용과 새로 형식화한 논증을 구별한다.

## 1. 대상과 계수 규약

고정된 정수 진법 `b ≥ 2`를 생각한다. 양의 정수 `a`의 표준 `b`진 전개를
최상위 자리부터 나열한 단어를 `digits_b(a)`라 하고, 그 길이를 `ℓ_b(a)`라 하자.
선행 0은 없다. `b^(ℓ−1) ≤ a < b^ℓ`이며 `ℓ = floor(log_b a)+1`이다.
Mathlib의 `Nat.digits`는 반대 순서이므로 실제 구현에는 뒤집기와 그 정확성 증명이 필요하다.

소수 `p₁=2 < p₂=3 < …`를 순서대로 이어 붙인 무한 숫자열을 `d`라 하자.
길이 `k ≥ 1`인 고정 단어 `w`와 유한 단어 `u`에 대해

\[
C_w(u)=\#\{i:0\le i,\ i+k\le |u|,\ (u_i,\ldots,u_{i+k-1})=w\}.
\]

겹치는 출현도 모두 센다. `|u|<k`이면 계수는 0이다. 정규성이란 모든 `k ≥ 1`과
모든 `w ∈ {0,…,b−1}^k`에 대해

\[
\frac{C_w(d[0:M])}{M}\longrightarrow b^{-k}\quad(M\to\infty)
\tag{N}
\]

인 것이다. 분모를 가능한 시작점 수 `M−k+1`로 잡아도 극한은 같지만,
이 문서와 구현 계약은 **분모 M**을 사용한다. `k=0`은 정규성의 양화 범위에서 제외한다.

아래 증명은 `b`를 고정한 채 진행된다. 첫 공개 목표는 `b=10`이다.
진법을 바꾸면 이어 붙여 얻는 실수도 바뀌므로 이것은 같은 실수의 절대 정규성 주장이 아니다.

## 2. 유한 평균의 4차 모멘트

확률 표기는 유한 집합의 균등 평균을 뜻한다. 측도론을 전제할 필요는 없다.
서로 독립인 Bernoulli(`p`) 변수 `I₁,…,I_m`에 대해 `Z_i=I_i−p`,
`S_m=Σ Z_i`, `v=E[Z_i²]`, `μ₄=E[Z_i⁴]`라 하자.
`E Z_i=0`, `|Z_i|≤1`이므로 `v≤1`, `μ₄≤1`이다.

독립성과 유한 평균의 곱 분해로 `E S_m=0`, `E S_m²=mv`다. 다음 전개에서
`E[S_m³ Z_{m+1}]`과 `E[S_m Z_{m+1}³]`는 각각 `E Z_{m+1}=0`, `E S_m=0`으로 사라진다.

\[
E S_{m+1}^4 = E S_m^4 + 6m v^2 + \mu_4.
\]

`m=0`에서 귀납하면

\[
E S_m^4=m\mu_4+3m(m-1)v^2\le 3m^2\quad(m\ge1).
\tag{M4}
\]

따라서 `η>0`, `m≥1`에 대해, 나쁜 표본에서는 `S_m⁴>η⁴m⁴`임을 이용하여

\[
\Pr(|S_m|>\eta m)\le\frac{3}{\eta^4m^2}.
\tag{T}
\]

이는 유한 합을 비교하는 부등식이다. 구현에서는 좌표별 유한 곱 공간의 평균과
`Finset.expect`를 우선 검토한다. `m=0`에서는 나누지 않으며 별도로 처리한다.

## 3. 빈도가 어긋나는 길이 ℓ의 단어는 드물다

`k,w`를 고정하고 `p=b^(−k)`라 하자. 길이 `ℓ`인 모든 `b^ℓ`개의 단어에 균등 평균을 취한다.
이 단계에서는 **선행 0을 허용한다**. 표준 정수 전개는 이 표본 공간의 부분집합이다.

유효한 시작점 `0≤i≤ℓ−k`를 `i mod k`에 따라 `k`개로 나눈다. 나머지가 `r`인
시작점의 수를 `m_r`, 그 시작점들에서 `w`가 출현한 횟수를 `Y_r`라 하자.
한 그룹 안의 길이 `k` 창들은 서로 겹치지 않으므로 그 지시변수들은 독립이며 성공 비율은 `p`다.
그룹들 **사이**의 독립성은 필요하지 않다.

`ℓ≥k`일 때

\[
C_w(u)=\sum_{r=0}^{k-1}Y_r,\qquad \sum_r m_r=\ell-k+1.
\]

고정 `ε>0`에 대해 `ℓ≥k`, `ℓ≥2(k−1)/ε`라 하자.
`τ=εℓ/(2k)>0`으로 놓는다. 모든 그룹에 `|Y_r−p m_r|≤τ`가 성립하면

\[
|C_w(u)-p\ell|
\le\sum_r|Y_r-pm_r|+p(k-1)
\le k\tau+(k-1)\le\varepsilon\ell.
\]

따라서 `|C_w(u)/ℓ−p|>ε`인 단어는 적어도 한 그룹에서 `|Y_r−p m_r|>τ`를 만족한다.
각 그룹은 실제 균등 곱 공간으로 옮길 수 있다. 사용한 좌표를 블록별로 나누고 남은 좌표를
보완 좌표로 분리하면, 전체 단어 공간은 블록 튜플과 보완 좌표 공간의 곱과 일대일 대응한다.
보완 좌표에 대한 균등 평균을 제거하면 블록 튜플에 대한 균등 평균을 얻는다.
이는 소수나 자릿수에 관한 독립성 가정이 아니라 유한 곱 집합의 계수 대응이다.

4차 모멘트 상계는 `m_r=0`일 때도 성립하며, `m_r≤ℓ`이므로
`E[(Y_r−p m_r)^4]≤3m_r²≤3ℓ²`다. 유한 Markov 부등식과 합집합 상계로 나쁜 단어의 비율은

\[
\sum_r\frac{3\ell^2}{\tau^4}
=\frac{48k^5}{\varepsilon^4\ell^2}.
\]

작은 양의 `ℓ`도 명시적으로 포함할 수 있다. 자연수 N을
`N≥k`, `εN≥2(k−1)`이 되도록 고르고
`K=48k⁵/ε⁴+N²+1`로 놓는다. `1≤ℓ<N`이면 나쁜 단어의 수는 전체 `b^ℓ`개 이하이며
`ℓ²≤N²<K`이므로 같은 상계가 적용된다. 따라서 모든 `ℓ≥1`에서

\[
\#\{u\in\{0,\ldots,b-1\}^{\ell}:|C_w(u)/\ell-p|>\varepsilon\}
\le K_{b,k,\varepsilon}\frac{b^\ell}{\ell^2}.
\tag{W}
\]

정규성은 고정된 `w`마다 증명하므로 모든 패턴에 대한 추가 합집합 상계는 필요 없다.
이 경로는 최적 상수를 목표로 하지 않는다. 처음 설계의 `192k³/ε⁴` 상수보다 크지만,
각 `m_r`의 양수성·하한을 따로 증명하지 않아도 되며 (W)의 결론은 동일하다.

## 4. X 이하의 나쁜 정수 개수

양의 정수 `a`가 나쁘다는 것은 `digits_b(a)`가 (W)의 조건을 위반한다는 뜻이다.
`B(X)`를 `1≤a≤X`인 나쁜 정수의 개수, `L=ℓ_b(X)`라 하자.
각 길이의 표준 정수 전개는 길이 ℓ의 단어 공간으로 단사적으로 들어간다.
따라서 (W)를 길이별로 합하면 `B(X)≤K Σ_{ℓ=1}^L b^ℓ/ℓ²`이다.
이 합은 다음 수렴 급수 하나로 제어할 수 있다.

\[
C_b=\sum_{j=0}^{\infty}(j+1)^2b^{-j}<\infty.
\]

`1≤ℓ≤L`, `j=L−ℓ`이면 `L=ℓ+j≤ℓ(j+1)`이므로

\[
\frac{b^\ell/\ell^2}{b^L/L^2}
=\left(\frac L\ell\right)^2 b^{-j}
\le(j+1)^2b^{-j}.
\]

`ℓ↦L−ℓ`가 단사라는 사실과 비음수 급수의 부분합 상계를 사용하면 모든 L≥1에서
`Σ_{ℓ=1}^L b^ℓ/ℓ²≤C_b b^L/L²`를 얻는다. `b^L≤bX`와
`log X < L log b`로 X>1에서

\[
B(X)\le KC_b\frac{b^L}{L^2}
\le KC_b b(\log b)^2\frac{X}{(\log X)^2}.
\tag{B}
\]

이 경로는 중간 길이를 기준으로 두 합을 나누는 초기 설계를 대체한다.
Lean에서는 정수 로그 길이 L을 유지한 상계로 구현해 아래 가중 길이 비율의 소멸에 직접 사용한다.
실수 로그로 쓴 (B)의 점근 표기를 별도 선언으로 내보내지는 않는다.
이는 모든 정수를 센 상계이므로 나쁜 **소수**에도 그대로 적용된다.

각 정수의 길이가 `L=O_b(log X)`이므로 나쁜 소수들이 기여하는 자릿수의 합 `D_bad(X)`는

\[
D_{\rm bad}(X)\le L B(X)=O_{b,k,\varepsilon}(X/\log X).
\tag{D}
\]

## 5. 전체 소수 자릿수는 적어도 X의 상수배다

`A_X`를 X 이하의 소수를 모두 이어 붙인 단어, `T_X=|A_X|`, `n=π(X)`라 하자.
`θ(X)=Σ_{p≤X} log p`인 Chebyshev 함수를 사용한다. 고정 Mathlib의
`Chebyshev.theta_ge`는 자연수 X에서 다음을 준다.

\[
\theta(X)\ge X\log2-\log(X+1)-2\sqrt X\log X.
\]

`log(X+1)=o(X)`, `√X logX=o(X)`이므로 충분히 큰 X에서
`θ(X)≥cX`, `c=(log2)/2>0`이다. 각 소수의 표준 전개는
`p<b^{ℓ_b(p)}`를 만족하므로 `log p≤ℓ_b(p) log b`이다. 합을 취하면

\[
T_X\log b\ge\theta(X)\ge cX,\qquad
T_X\ge\frac c{\log b}X.
\tag{L}
\]

경계 개수는 Chebyshev의 소수 계수 상계로 제어한다. 충분히 큰 X에서
`π(X)≤(log4+1)X/logX`이므로

\[
\frac n{T_X}\le
\frac{(\log4+1)\log b}{c\log X}\longrightarrow0.
\tag{E}
\]

이 단계는 소수정리의 점근 등식을 사용하지 않는다. 초기 설계에서는
`π(X)≥cX/logX`와 √X 컷오프로 (L)을 얻었으나, 구현에서는 기존 θ 정리와
소수 계수 상계를 재사용하는 위 경로를 택했다. M1c의 소수 계수 하한 정리는
그대로 유효하지만 이 경로의 필수 의존성은 아니다. 이 절의 연결은 `PrimeDigitMass`와 `PrimePrefixBounds`에 구현했다.

## 6. 항 내부·나쁜 항·경계의 세 오차

유한 단어 `u,v`에 대해

\[
0\le C_w(uv)-C_w(u)-C_w(v)\le k-1.
\tag{J}
\]

차이는 두 단어의 접합점을 가로지르는 출현의 수이며, 가능한 시작점은 많아야 `k−1`개다.
빈 단어 또는 짧은 단어도 이 부등식을 만족한다.
반복 적용하면 `A_X`에서 소수 사이 경계를 가로지르는 출현은 많아야 `(k−1)(n−1)`개다.

좋은 소수의 내부 오차는 `εℓ_b(p)` 이하, 나쁜 소수의 내부 오차는
`|C_w(digits_b(p))−p_0 ℓ_b(p)|≤ℓ_b(p)` 이하이다. 여기서 빈도 상수는
소수 기호와 구별하여 `p_0=b^(−k)`라 쓴다. 따라서

\[
|C_w(A_X)-p_0T_X|
\le\varepsilon T_X+D_{\rm bad}(X)+(k-1)n.
\tag{F}
\]

(D),(L),(E)로 나누면 `limsup |C_w(A_X)/T_X−p_0|≤ε`이다.
임의 `ε>0`에 대해 성립하므로 이 오차는 0으로 수렴한다.
`ε`에 의존하는 상수와 시작점이 있어도, 먼저 `ε`를 고정하고 `X→∞`를 취하므로 문제없다.

## 7. 소수 중간에서 끊은 모든 접두사

지금까지는 소수를 온전히 붙인 경계만 다뤘다. 이 부분을 생략하면 (N)의 증명이 아니다.
임의의 큰 접두사 길이 `M`에 대해 `p_n`까지의 길이 `T_n≤M<T_{n+1}`인 `n`을 잡고,
`X=p_n`, `t=M−T_n`라 하자. Bertrand 공준으로 `p_{n+1}≤2X`이므로

\[
0\le t<\ell_b(p_{n+1})\le 1+\log_b(2X)=O_b(\log X).
\]

(L)에서 `T_n≥c'X`이므로 `t/T_n→0`. 길이 `t`를 덧붙이면 새로 완전히 포함되는
블록은 많아야 `t`개이므로 `0≤C_w(d[0:M])−C_w(d[0:T_n])≤t`이다. `C_w(d[0:T_n])≤T_n`으로

\[
\left|\frac{C_w(d[0:M])}{M}-\frac{C_w(d[0:T_n])}{T_n}\right|
\le\frac{2t}{M}\le\frac{2t}{T_n}\longrightarrow0.
\]

`M→∞`이면 `n→∞`이며, 6절의 경계 수렴과 결합하여 (N)을 얻는다.
Bertrand 대신 소수 계수 하한으로 다음 소수의 자릿수 성장을 제어할 수도 있지만,
이미 있는 더 직접적인 정리를 재사용하는 경로를 선택한다.

## 8. 숫자열에서 실제 상수로

숫자열 `d`에 대해

\[
x_b=\sum_{j=0}^{\infty}\frac{d_j}{b^{j+1}}
\]

를 정의한다. 항은 비음수이고 기하급수로 지배되어 급수는 수렴한다.
(N)의 `k=1` 경우에서 0도, 1도 무한히 많이 나타난다.
따라서 숫자열은 어느 지점부터 전부 `b−1`이거나 전부 0이 될 수 없다.

처음 `N`자리의 정수 값을 `V_N`이라 하면 `b^N x_b=V_N+R_N`이고

\[
R_N=\sum_{j=N}^{\infty}d_j b^{N-j-1},\qquad 0<R_N<1.
\]

양수성은 뒤에 나타나는 1에서, 엄격한 상계는 뒤에 나타나는 0과 기하급수 상계에서 나온다.
그러므로 `floor(b^N x_b)=V_N`이며 모든 표준 `b`진 자리 숫자가 실제로 `d_j`와 일치한다.
반복되는 9와 유한 소수 표현의 모호성도 제거된다. 따라서 `x_b`는 `b`진 정규수다.

특히 `b=10`이면 `x_b=0.235711131719…`이고 십진 정규성이 성립한다. □

## 증명 검토와 범위

- 겹치는 출현을 모두 세며, 독립성은 나머지 그룹 **내부**에만 사용했다.
- 모든 정수를 세는 단계의 선행 0 허용과 실제 정수 전개의 선행 0 금지를 구별했다.
- 각 소수의 끝자리 편향은 (E)의 경계 밀도 소멸과 양립한다. 그것만으로 정규성이 증명되지는 않는다.
- 고정 길이, 임의 정수 컷오프, 소수 경계, 임의 접두사, 실수 전개의 연결을 각각 다뤘다.
- 4차 모멘트 경로는 소수의 Chebyshev 밀도에 충분하다. 원 논문의 모든 증가수열에 대한
  일반 정리를 이 더 약한 예외 집합 상계로 얻었다고 주장하지 않는다.
- 최종 수렴과 실제 실수 연결까지의 Lean 선언은 [증명 지도](proof-map.md)에 대응시켰다.

## 구현 대응 (M1a)

파일: [`CopelandErdos/Words/Occurrences.lean`](../CopelandErdos/Words/Occurrences.lean).
namespace: `CopelandErdos.Words`. 모든 선언은 generic `List α`와 `[DecidableEq α]`를 사용한다.

| 종이 계약 | Lean 선언 |
|---|---|
| 유효 시작점과 패턴 일치 | `OccursAt` |
| 겹치는 출현 계수와 cardinality | `occurrenceCount`, `occurrenceCount_eq_card`, `occursAt_start_lt` |
| `C_w(u)≤\|u\|` | `occurrenceCount_le_length` |
| host가 패턴보다 짧으면 0 | `occurrenceCount_eq_zero_of_length_lt` |
| (J)의 하한 | `occurrenceCount_add_le_append` |
| (J)의 상한, `w≠[]` | `occurrenceCount_append_le` |
| 7절의 append 길이 t 상계 | `occurrenceCount_le_append`, `occurrenceCount_append_le_add_length` |

빈 패턴의 계수를 0으로 정의한 것은 구현상의 명시적 확장이다. 이 문서의 정규성은 여전히
양의 길이 패턴만 다룬다. (J)의 자연수 차이만 제시하지 않고, 뺄셈 전의 하한·상한을 각각 증명했다.
[검증 기록](verification-m0-m1a.md)에 실제 빌드와 공리 감사 범위를 적었다.

## 구현 대응 (M1b·M1c)

파일: [`Probability/FiniteMoments.lean`](../CopelandErdos/Probability/FiniteMoments.lean),
namespace `CopelandErdos.Probability`.
구현은 Bernoulli만을 위한 식보다 일반적인 형태다. 비어 있지 않은 유한 α에서
평균이 0인 함수 `f : α → ℝ`와 실제 곱 공간 `Fin m → α`를 사용한다.

| 종이 계약 | Lean 선언 |
|---|---|
| 균등 평균 = 유한 합 / 원소 수 | `uniformMean_eq_sum_div_card` |
| 곱 공간의 평균 분해 | `uniformMean_product`, `uniformMean_succ` |
| 1·2·4차 모멘트 등식 | `mean_coordinateSum`, `mean_coordinateSum_sq`, `mean_coordinateSum_fourth` |
| (M4)의 상계, 점별 `abs(f)≤1` | `mean_coordinateSum_fourth_le` |
| 유한 Markov 부등식 | `uniformMean_card_le` |
| (T)의 실제 사건 원소 수 비율 | `coordinateSum_tail_card_le` |

정확한 모멘트 등식은 m=0도 포함하며, 꼬리 상계에는 m≥1과 η>0이 필요하다.
M2a에서 `α = Fin k → Fin b`, `f(a)=1[a=w]−1/card α`에 대한 중심화와
절댓값 조건, 비중첩 블록 그룹과 균등 곱 공간 사이의 계수 대응까지 증명했다.

파일: [`NumberTheory/PrimeBounds.lean`](../CopelandErdos/NumberTheory/PrimeBounds.lean),
namespace `CopelandErdos.NumberTheory`.

| 종이 계약 | Lean 선언 |
|---|---|
| c=(log 2)/2의 양수성 | `primeCountingLowerConstant_pos` |
| 충분히 큰 자연수 X에서의 소수 계수 하한 | `eventually_primeCounting_ge` |
| 양의 상수 존재 형태의 하한 | `exists_pos_eventually_primeCounting_ge` |
| 인접한 소수의 q≤2p | `consecutive_prime_le_two_mul` |
| 증가하는 소수 나열에의 적용 | `nth_prime_succ_le_two_mul` |

소수 하한은 Mathlib의 `Chebyshev.pi_ge`에서, 인접 소수 상계는 Bertrand 정리에서 도출했다.
소수정리나 추가 미증명 가정은 사용하지 않았다. [통합 검증](verification-m1b-m1c.md)을 참고한다.

고전 정리의 출처: A. H. Copeland and P. Erdős, *Note on Normal Numbers* (1946),
[원문](https://users.renyi.hu/~p_erdos/1946-01.pdf). 본 문서의 4차 모멘트 전개는
형식화 범위를 줄이기 위해 여기서 택한 별도의 증명 설계이며 새로운 정리나 최초 증명이라는 주장이 아니다.

## 구현 대응 (M2a·M2b)

| 종이 계약 | Lean 선언 |
|---|---|
| 단사 좌표 제한의 균등 평균 보존 | `Words.uniformMean_restrict` |
| 비중첩 그룹의 좌표 단사성 | `Words.blockPosition_injective` |
| 모든 겹치는 출현의 나머지 그룹 분해 | `Words.occurrenceCount_eq_sum_residueCount` |
| 전체 단어 공간에서 그룹의 4차 모멘트 상계 | `Words.mean_residueDeviation_fourth_le` |
| (W), 짧은 길이까지 포함 | `Words.exists_badWords_card_le` |
| 표준 소수 전개, 선행 0 없음 | `Digits.primeBlock`, `Digits.head_primeBlock_ne_zero` |
| 실제 무한 스트림과 유한 flatten 일치 | `Digits.ofFn_primeDigits_cumulativeLength` |
| 실제 십진 스트림의 첫 여섯 자리 | `Digits.ofFn_primeDigits_six` |

선언 앞에 `CopelandErdos.`를 붙인다. (W)는 충분히 큰 길이에서 `48k⁵/ε⁴`를
사용하고 유한한 작은 길이를 K에 흡수한다. 최적 상수를 주장하지 않는다.
[통합 검증 기록](verification-m2.md) 참조. 이 결과만으로 (N)이나 실수 정규성이 완성된 것은 아니다.
