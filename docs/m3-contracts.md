# M3 구현 계약

후속 상태: 아래는 구현 전 계약의 기록이다. 2026-11-18 최종 구현·검증을 완료했다. [검증 기록](verification-complete.md)과 [실제 선언 대응](proof-map.md)을 따른다.

2026-11-18. 메인 Astra의 수학적 계약이다. 아래에서 “예정”인 항목은
Lean으로 증명된 결과가 아니며, 실제 완료 기록은 별도 검증 문서에 남긴다.

## 진행 중인 세 모듈

1. `Digits/NatWord`, `NumberTheory/BadIntegers`:
   `natWord b hb a`는 a의 표준 최상위 자리 우선 전개다. a=0은 빈 목록이다.
   역방향 `Nat.ofDigits` 복원으로 단사성을 얻는다.
   `badIntegersOfLength ... ℓ X`는 **a<X**인 양의 정수 중 길이가 ℓ이고
   기존 겹침 계수의 정규화 오차가 ε보다 큰 것들을 센다.
   모든 X와 ℓ≥1에 하나의 K로 `card≤K*b^ℓ/ℓ²`를 증명한다.
2. `Analysis/GeometricBounds`:
   b>1이면 모든 L≥1에 `Σ_{n=1}^L b^n/n²≤C*b^L/L²`인 C>0이 존재한다.
   증명은 j=L−n, L≤n(j+1), 수렴 급수 `Σ(j+1)²/b^j`를 사용한다.
3. `Words/Concatenation`:
   유한 단어 목록의 총 오차를 좋은 항의 ε·총길이, 나쁜 항의 총길이,
   `(패턴길이−1)·항수`의 합으로 제한한다. 빈 항을 허용하고 중복 항의 길이를 보존한다.
   뒤에 t자리 붙일 때 정규화 빈도 차이는 기존 길이 T>0에서 `2t/T` 이하이다.

## 다음 연결: 전체 예외 정수와 가중 길이

`badIntegersBelow ... X`는 양의 a<X 중 실제 길이로 정규화한 오차가 ε보다 큰 정수다.
X>0에 대해 L=Nat.log b X+1로 잡으면 모든 a<X의 길이가 L 이하이다.
정수들을 길이별로 분할하여

`card(badIntegersBelow ... X) ≤ K*C_b*b^L/L²`

를 얻는다. `b^L≤bX`이므로 X>1에서 `O(X/log²X)`가 따른다.
실제 최종 적용은 소수 p까지 포함하므로 cutoff를 p+1로 쓰거나,
별도 inclusive 집합을 정의해 exclusive 경계를 명시적으로 변환한다.
나쁜 소수는 이 집합의 부분집합이고 각 길이는 L 이하이므로 가중 길이는
`L*card(badIntegersBelow ... X)` 이하이다. 중복이 없는 소수 나열과
Finset 사이의 대응을 증명해야 하며, 이를 가정으로 남기지 않는다.

## 전체 소수 길이: 사용할 수 있는 두 경로

종이 증명 5절은 π(X)의 하한과 √X 컷오프로 총길이 T(X)≥cX를 얻는다.
고정 Mathlib에는 더 직접적인 다음 정리도 있다.

- `Chebyshev.theta_ge`: θ(X)≥X log2−log(X+1)−2√X logX.
- `Chebyshev.theta_eq_sum_primesLE_log`: θ(X)=Σ_{p≤X}log p.
- `Chebyshev.eventually_primeCounting_le`: π(X)≤(log4+δ)X/logX, 충분히 큰 X.

대안 구현은 log(X+1)=o(X), √X logX=o(X)를 써서 θ(X)≥(log2/2)X를 얻는다.
각 소수에 `log p≤length_b(p)*log b`를 적용하면
`T(X)≥θ(X)/log b≥log2/(2log b)*X`이다.
위 π 상계로 `π(X)/T(X)→0`도 바로 얻는다.
이 대안은 소수정리를 사용하지 않지만 종이 증명의 원래 경로보다 기존 Mathlib 정리를
더 재사용한다. 실제 채택 시 종이 증명과 구현 매핑을 함께 갱신한다.

## 마지막 조립의 필수 조건

- 고정 패턴, 모든 ε>0에서 나쁜 소수 가중 길이 / T(X) →0.
- 소수 경계의 계수 오차를 총길이로 나눈 값 →0.
- 임의 접두사 M을 포함하는 실제 BlockStream의 블록 인덱스가 M과 함께 무한대로 감.
- 다음 소수≤직전 소수의 두 배, 다음 소수 길이=O(log p), T≥cp를 사용하여
  잘린 마지막 블록 길이/T→0.
- 위 결과를 조립한 최종 stream 정리에는 예외 계수·밀도·수렴 가정을 남기지 않는다.

실수 연결 M4에서는 `Real.ofDigits`를 사용하되 Mathlib의 `Real.ofDigits_digits`는
필요한 역방향 등식과 다르다. 모든 꼬리에서 0과 1의 존재를 정규성으로 얻고,
꼬리 값이 (0,1)에 있음을 증명하여 `Real.digits (Real.ofDigits d) b = d`를 별도로 연결한다.
