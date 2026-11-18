# Copeland–Erdős 상수의 Lean 형식화

`0.235711131719…`의 **십진 정규성을 추가 수학 가정 없이 Lean으로 증명했다.**
소수를 실제로 이어 붙인 숫자열, 모든 접두사의 겹치는 패턴 빈도 수렴,
그 숫자열과 표준 실수 전개의 일치까지 포함한다.

```lean
import CopelandErdos
open CopelandErdos.Normality

example : NormalInBase 10 copelandErdos := copelandErdos_normal
```

`NormalInBase 10 copelandErdos`는 상수가 [0,1)에 속하고, 표준 십진 전개에서
모든 길이 k>0의 패턴 w의 빈도가 `1/10^k`로 수렴한다는 뜻이다.
분모는 전체 접두사 길이 M이며, 모든 자연수 M을 따라 극한을 취한다.
`copelandErdos_pos`, `copelandErdos_lt_one`, `digits_copelandErdos`도 제공한다.
양화사를 펼친 정리는 `tendsto_copelandErdos_patternFrequency`다.

## 증명 경로

유한 균등 단어 공간의 4차 모멘트로 예외 단어를 `K*b^ℓ/ℓ²`개 이하로 제한한다.
이를 표준 정수 전개로 옮겨 예외 소수들이 차지하는 자릿수 비율이 0으로 감을 보인다.
Chebyshev와 Bertrand 정리로 접합 경계와 마지막 불완전 블록의 영향을 제어한다.
마지막으로 `Real.ofDigits`의 값을 표준 `Real.digits`로 읽었을 때 원래 숫자열이 복원됨을 증명한다.
**소수 숫자의 독립성이나 소수정리는 가정하지 않는다.**

- [종이 증명](docs/proof.md)
- [증명 지도와 선언 대응](docs/proof-map.md)
- [공개 사용 예제](examples/Normality.lean)
- [최종 검증 기록](docs/verification-complete.md)
- [Mathlib 최초 조사](docs/mathlib-audit.md)
- [구현 계획과 경과](docs/implementation-plan.md)
- [Continuous AI 도입 상태](docs/continuous-ai-adoption.md)

## 검증

Lean `v4.35.0`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`에 고정했다.
2026-11-18 pod 통합 빌드, 새로 실행한 공리 감사, 공개 예제를 통과했다.
23개 라이브러리와 루트의 **472개 선언**을 비공개 보조정리까지 감사했으며,
사용 공리는 `propext`, `Classical.choice`, `Quot.sound`뿐이다.
선언 수는 생성·비공개 선언을 포함하며 정리의 개수와 다르다.

준비된 Lean 환경에서:

```sh
python3 -I scripts/check_lean_inventory.py
python3 -I scripts/check_combinatorics.py
lake build
lake env lean CopelandErdosAudit.lean
lake env lean examples/Normality.lean
```

개발 환경의 무거운 빌드는 `rdev x bertha-ultra --task ce-geometric -- lake build`로
실행했다. Python의 유한 검사는 별도의 회귀 검사이며 일반 정리의 증명이 아니다.
GitHub CI는 같은 빌드·검사를 실행하도록 구성했다. 원격 실행 결과와 자동화 상태는
[도입 기록](docs/continuous-ai-adoption.md)에서 구별한다.

## 범위와 배경

고정 진법 b≥2에서 그 진법으로 소수를 이어 붙인 숫자열의 정규성도 일반형으로 증명했다.
진법을 바꾸면 만들어지는 실수가 달라진다. 같은 상수의 모든 진법 정규성이나
Smarandache–Wellin 소수의 무한성을 증명한 것은 아니다.

블로그 「소수를 이어 붙이면 생기는 두 가지 이야기」를 위한 수학적 후속 프로젝트다.
증명 설계·계약·소스 검토는 메인 Astra, 구현은 사용자 지정 `gpt-6.1-sol` / `xhigh`
작업자가 담당했다. Continuous AI의 제안·검토 실행과 이번 형식화 구현을 구분한다.

고전 정리: Copeland and Erdős, *Note on Normal Numbers*, Bull. Amer. Math. Soc. 52 (1946),
857–860. [원 논문](https://users.renyi.hu/~p_erdos/1946-01.pdf).
여기서는 소수에 목표를 한정한 4차 모멘트 증명 경로를 별도로 사용한다.
원 논문의 더 일반적인 수열 정리를 그대로 형식화했다거나 최초 형식화라고 주장하지 않는다.
