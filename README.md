# Copeland–Erdős 상수의 Lean 형식화 설계

목표는 `0.235711131719…`의 **십진 정규성**을 추가 가정 없이 Lean으로 증명하는 것이다.
현재 상태는 **증명 설계 및 Mathlib 의존성 조사 단계**다. Lean 정규성 정리를 구현하거나
컴파일한 저장소가 아니며, Continuous AI도 아직 배포하지 않았다.

- [Pencil-and-paper 증명](docs/proof.md): 유한 평균의 4차 모멘트와 Chebyshev 하한을 사용하는 경로.
- [Mathlib 조사](docs/mathlib-audit.md): 조사한 정확한 버전, 재사용 선언, 남은 구현.
- [구현 및 Continuous AI 계획](docs/implementation-plan.md): 작업 계약, 순서와 완료 조건.
- [유한 조합 검사](docs/computational-checks.md): 작은 사례의 회귀 검사. 일반 증명과 구별한다.

블로그 「소수를 이어 붙이면 생기는 두 가지 이야기」의 수학적 후속 프로젝트다.
정규성은 숫자 블록의 빈도에 관한 명제다. Smarandache–Wellin 소수의 무한성을
증명하거나, 이 상수가 모든 진법에서 정규수임을 주장하는 프로젝트가 아니다.

전체 설계·종이 증명·정리 명세는 메인 Astra가 담당한다. 실제 구현은 사용자가 지정한
`gpt-6.1-sol` / `xhigh` 작업자에게 파일 소유권과 명시적 정리 계약을 주어 맡긴다.

기준 조사일: 2026-11-17. 소스 조사 대상은 Lean v4.35.0,
Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`다.
아직 Lake 프로젝트의 의존성을 설치하거나 이 버전을 프로젝트 lockfile로 고정하지 않았다.

## 근거

Copeland and Erdős, *Note on Normal Numbers*, Bull. Amer. Math. Soc. 52 (1946), 857–860:
[원 논문](https://users.renyi.hu/~p_erdos/1946-01.pdf).
원 논문은 더 일반적인 수열 정리를 증명한다. 여기서는 소수에 목표를 한정한
4차 모멘트 경로를 별도로 전개하며, 그 경로가 원 논문에 그대로 적혀 있다고 주장하지 않는다.
