# M4 실수 전개 연결 계약

후속 상태: 아래는 구현 전 계약의 기록이다. 2026-11-18 최종 구현·검증을 완료했다. [검증 기록](verification-complete.md)과 [실제 선언 대응](proof-map.md)을 따른다.

메인 Astra의 구현 전 설계. 아직 이 문서의 정리가 Lean으로 구현됐다는 뜻은 아니다.
진법 b≥2와 실제 숫자열 d:ℕ→Fin b에 대해 아래 보조정리를 사용한다.

## 1. 모호한 전개를 제외하는 충분조건

`∀N,∃j≥N, d j < b−1`이면 모든 꼬리의 `Real.ofDigits` 값은 1보다 작다.
증명: 모든 항을 상수 숫자열 b−1의 항으로 위에서 제한하고, 가정이 주는 한 위치에서
엄격한 부등식을 얻는다. 양쪽 급수는 `Real.summable_ofDigitsTerm`으로 수렴한다.
상수 b−1의 값은 `Real.ofDigits_const_last_eq_one'`로 1이다.

추가로 `∀N,∃j≥N, 0<d j`이면 모든 꼬리의 값은 양수다.
비음수 급수의 한 양수 항으로 충분하다. 표준 자리 복원에는 비음수성과 <1만 필요하며,
엄격한 양수성은 최종 상수의 `0<x`에 사용한다.

## 2. 유한 자리 값과 floor

자연수 V를 `V 0=0`, `V(n+1)=b*V n+(d n).val`로 정의한다.
`x=Real.ofDigits d`, `R_n=Real.ofDigits (fun i=>d(i+n))`로 놓으면

`b^n*x = V n + R_n`

을 증명한다. `Real.ofDigits_eq_sum_add_ofDigits`와 유한합 귀납으로 연결한다.
`0≤R_n<1`이므로 `Nat.floor(b^n*x)=V n`이다.
따라서 `Real.digits x b n`의 정의에 들어가는 자연수 floor를 바꾸면

`floor(x*b^(n+1)) % b = V(n+1)%b = (d n).val`

이 되어 `Real.digits (Real.ofDigits d) b=d`를 얻는다.
`Real.ofDigits_digits`는 역방향이므로 이 단계를 대체하지 못한다.

## 3. 정규성에서 충분조건 얻기

모든 비어 있지 않은 패턴의 겹침 빈도가 b^(−k)로 수렴한다는 것을
`NormalDigits d`의 뜻으로 삼는다. 각 c:Fin b의 singleton 패턴에 적용하면
c가 모든 꼬리에 나타난다. 만약 N 이후 c가 없다면 모든 길이 M의 해당 계수는 N 이하이고,
빈도는 N/M→0이다. 이것은 양수 1/b로 수렴한다는 사실과 모순이다.

c=0은 모든 꼬리에서 b−1보다 작은 숫자를, c=1은 양수 숫자를 준다.
따라서 `NormalDigits d`에서 `0<Real.ofDigits d<1`과 표준 숫자 복원 등식을 얻는다.

## 4. 최종 계약

`copelandErdos := Real.ofDigits (Digits.primeDigits 10 (by decide))`.
최종 정리는 (1) 모든 k≥1과 w:Fin k→Fin10에 대한 표준 십진 자리의 빈도 수렴,
(2) `Real.digits copelandErdos 10 = Digits.primeDigits 10 ...`,
(3) `0<copelandErdos<1`을 모두 제공한다.
최종 정리에 `NormalDigits`, 예외 단어 상계, 소수 밀도 같은 가정을 남기지 않는다.
