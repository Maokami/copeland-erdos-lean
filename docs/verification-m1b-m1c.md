# M1b·M1c 검증 기록

날짜: 2026-11-18. 두 구현 작업자는 사용자 지정 `gpt-6.1-sol` / `xhigh`를 사용했다.
메인 Astra가 사전에 수학적 계약을 확정하고, 완성 소스와 가정을 검토한 뒤 통합 빌드를 재실행했다.

## M1b: 유한 곱 공간의 모멘트

파일: `CopelandErdos/Probability/FiniteMoments.lean`.
비어 있지 않은 유한 α와 평균이 0인 `f : α → ℝ`에 대해
`Ω_m = Fin m → α`, `S_m(x)=Σ_i f(x_i)`를 사용한다.
평균은 `Finset.expect`로 정의하며, 유한 합/cardinality와 같다는 정리도 제공한다.

증명한 내용:

- 실제 곱 공간과 `Fin.consEquiv`를 통한 head/tail 평균 분해.
- `E S_m=0`, `E S_m²=m E f²`.
- `E S_m⁴=m E f⁴ + 3m(m−1)(E f²)²`. m−1은 실수 뺄셈이며 m=0도 포함한다.
- 점별 `|f|≤1`이면 `E S_m⁴≤3m²`.
- 비음수 함수의 유한 Markov 부등식과, m≥1·η>0에서
  `#{x: |S_m(x)|>ηm}/card Ω_m ≤ 3/(η⁴m²)`.

독립성을 불명확한 가정으로 받지 않고 실제 균등 곱 공간의 평균을 분해했다.
평균 0과 점별 유계성은 관측 함수에 필요한 정상적인 조건이다. 다음 단계에서는
블록 지시함수에 대해 이 조건과 곱 공간 대응을 별도로 증명해야 한다.
소수 자릿수의 독립성을 가정하거나 증명한 결과가 아니다.

작업자의 단독 파일 검사(exit 0, 경고 없음), 모듈 빌드(1141 jobs), 주요 선언 9개에 대한
직접 공리 출력이 통과했다. 메인은 아래 통합 빌드로 전체 선언을 다시 감사했다.

## M1c: 소수 개수와 다음 소수

파일: `CopelandErdos/NumberTheory/PrimeBounds.lean`.

- 명시적 상수 `c=Real.log 2/2`와 양수성.
- 자연수 n에 대해 충분히 큰 n에서 `c*n/log n ≤ Nat.primeCounting n`.
- 위 하한의 양의 상수 존재 형태.
- 인접 소수 p,q에 대해 `q≤2p`.
- 추가 인접성 가정 없이 `Nat.nth Nat.Prime (n+1) ≤ 2*Nat.nth Nat.Prime n`.

Chebyshev 보정항은 `log(n+1)=o(n)`에서 제어하고, 최종 나눗셈에는 n>1을 확보했다.
연속 소수에 관한 정리는 Mathlib의 Bertrand 정리와 nth-prime API로 연결한다.
새 소수정리 증명이나 미증명 수학 가정은 없다.

작업자의 모듈 빌드(2868 jobs)와 공개 선언 7개의 공리 출력이 통과했다.

## 통합 및 메인의 재실행

두 모듈을 루트의 `public import`와 공리 감사의 직접 `import all` 목록에 추가했다.
기존 `Words/Occurrences.lean`은 수정하지 않았다.

메인이 실행한 명령:

```sh
python3 -I scripts/check_lean_inventory.py
lake build
git diff --check
```

직접 관찰한 결과(exit 0):

```text
Lean inventory passed: 3 library source(s), root and audit connected
Axiom audit passed: 4 modules, 84 declarations; axioms: [Quot.sound, Classical.choice, propext]
Build completed successfully (2874 jobs).
```

재실행에서 감사 결과는 `Replayed`로 표시됐다. 84는 비공개·생성 선언까지 포함한 감사 대상 수이며,
새 정리의 수가 아니다. jobs 수에는 의존성과 캐시 작업이 포함된다.
감사 구현의 음성 검사는 M0에서 수행했으며, 이번에는 그 검사를 반복하지 않고
동일한 감사 구현의 import-all 범위를 두 새 모듈로 확장했다.

## 검증 소스

메인이 확인했고 작업자의 검증 파일과도 일치한 SHA256:

```text
b352bf14fad13d0222c02160e67effa29452f2a2ca0a426d8e14c377f33fbe88  CopelandErdos.lean
8cb0565e2df181ed99547aa794f8160010cc4c876291c5cade3cab7e57b79a96  CopelandErdosAudit.lean
e1fb546b7f14ca270bc29d07138883fc05b7ffcf911e5d56e9944dc61b2e3eb7  CopelandErdos/Probability/FiniteMoments.lean
f8dbb20f6f01a5984ffaebf49d62d4a551ee8d2d8d755b5f552bc9297ed8ca68  CopelandErdos/NumberTheory/PrimeBounds.lean
```

Lean v4.35.0 / Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`는 변경하지 않았다.
이번 변경은 로컬 미커밋 상태이며 원격 게시하지 않았다.

## 남은 범위

M2a의 블록 분할·균등 곱 공간 대응·나쁜 단어 개수 상계, M2b의 소수 스트림,
M3의 전체 극한, M4의 실수 자리 전개 연결은 아직 남아 있다.
따라서 아직 **Copeland–Erdős 상수의 정규성 전체를 Lean으로 증명한 것은 아니다.**
