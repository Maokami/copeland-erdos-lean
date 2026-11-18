# 구현 및 Continuous AI 계획

상태: **M0–M4의 수학 구현과 최종 통합 검증 완료** (2026-11-18).
M5의 공개 예제·증명 지도·CI 설정도 마련했다. 원격 실행·Continuous AI pilot은
[도입 기록](continuous-ai-adoption.md)에서 별도로 추적한다.
[최종 검증 기록](verification-complete.md)에 실제 증거를 적었다.

## 1. 최종 계약

소수를 증가하는 순서로, 선행 0 없이, 최상위 자리부터 이어 붙인 스트림을 `primeDigits 10`이라 한다.
`copelandErdos := Real.ofDigits (primeDigits 10)`로 실수를 정의한다.

최종 결과는 두 부분 모두 필요하다.

1. 모든 `k≥1`, `w : Fin k → Fin 10`에 대해 첫 `M`자리의 겹치는 블록 빈도가 `10^(−k)`로 수렴.
2. `Real.digits copelandErdos 10 = primeDigits 10`과 `0 < copelandErdos < 1`.

`PrimeDensity`, `BadWordBound`, `Normality` 같은 핵심 명제를 매개변수로 받는 중간 정리는
모듈 분리에 쓸 수 있지만, 최종 정리에 그 매개변수를 남기면 프로젝트 완료가 아니다.
정의에 결론을 끼워 넣거나 일반적인 정규수와 다른 의미를 쓰지 않도록 자연어 명세와 대조한다.

## 2. 역할 및 변경 소유권

- **메인 Astra:** 전체 계획, 종이 증명, 선언의 가정·양화사, 위험한 설계 변경, 통합 및 수학적 검토.
- **구현 작업자:** 사용자 지정 `gpt-6.1-sol`, reasoning `xhigh`. 각 작업마다 담당 파일과
  변경할 수 없는 정리 계약을 전달한다. 다른 작업자의 편집을 되돌리지 않는다.
- **검증:** Lean 컴파일·공리 감사와 정의/종이 증명의 의미 대조를 구별한다.
  AI의 "증명 완료" 보고만으로 완료 처리하지 않는다.

## 3. 마일스톤과 시작 가능한 작업

| 단계 | 예정 모듈 | 구체 산출물 | 의존성 |
|---|---|---|---|
| M0 | Lake 설정·감사 | 정확한 Lean/Mathlib pin, 최소 build, 모든 라이브러리 선언의 공리 감사 | 현재 소스 조사 |
| M1a | `Words/Occurrences` | 겹치는 출현 정의, `count≤length`, append 차이 `0..k−1`, append 길이 t의 증가≤t | M0 |
| M1b | `Probability/FiniteMoments` | 유한 곱 평균의 2차·4차 모멘트 귀납식, `E S⁴≤3m²`, 유한 Markov 상계 | M0 |
| M1c | `NumberTheory/PrimeBounds` | Chebyshev에서 eventual `cX/log X` 하한, Bertrand의 연속 소수 버전 | M0 |
| M2a | `Words/BadWords` | 시작점의 mod-k 분할·같은 그룹의 비중첩, 나쁜 길이 ℓ 단어≤`K b^ℓ/ℓ²` | M1a, M1b |
| M2b | `Digits/PrimeStream` | `Nat.digits` reverse, 누적 길이, 무한 스트림, prefix와 유한 flatten의 일치 | M1a |
| M3 | `Normality/PrimeConcatenation` | 나쁜 정수≤`O(X/log²X)`, 전체 자릿수≥`cX`, 경계 오차, 모든 접두사 수렴 | M1c, M2a, M2b |
| M4 | `Normality/RealBridge` | `Real.ofDigits`의 표준 자리 일치, 십진 상수의 무조건부 정규성 | M3 |
| M5 | blueprint·release | 선언 연결, 전체 build와 공리 감사, 문서의 가정 점검, 블로그용 예제 | M4 |

**완료된 구현:** M3는 예외 정수의 정수 로그 길이 상계, Chebyshev θ를 통한
총자릿수 하한, 경계·다음 블록 비율의 소멸을 실제 소수 숫자열에 연결했다.
M4는 정상 숫자열의 재등장 성질로 표준 실수 전개를 복원했다.
최종 정규성 명제에 미증명 수학 가정은 남아 있지 않다.
이제 공개 CI 및 Continuous AI 검토 pilot을 검증한다. 승인되지 않은 새 수학 목표를
자동으로 시작하지 않는다.

### 작업별 고정 계약 예

- Occurrences: `k=0`은 주 정리에서 제외; 빈 단어와 `length<k`는 계수 0; 모든 겹침 포함.
- FiniteMoments: 유한 **균등 곱 공간**의 좌표 독립성만 사용. 소수의 숫자가 독립이라는 가정 금지.
  `m=0`에서 나눗셈하지 않는다. 확률 표기의 측도론 버전으로 바꿀 때는 메인과 명세를 재대조한다.
- BadWords: 모든 길이-ℓ 단어에 선행 0 허용; 표준 정수 전개로 제한할 때는 단사성으로 상계 전달.
- PrimeStream: 양의 블록 길이, 증가하는 누적 길이, 모든 위치의 존재·유일성을 증명한다.
- PrimeConcatenation: 끝나는 소수 경계에 대한 수렴에서 멈추지 않는다. 임의의 M까지 증명한다.
- RealBridge: 정규성에서 무한히 많은 0/1을 얻어 꼬리의 모호성을 제거한다.

## 4. 비용과 환경

- 기존 Kuratowski와 호환되는 Mathlib SHA를 M0에서 실제 lockfile로 고정했다.
- 새 `.lake/packages`는 같은 버전이 있는 sibling에서 APFS clone으로 시드한다.
  `cp -R`, `rsync`, worktree별 새 Mathlib 다운로드를 하지 않는다.
- 무거운 빌드/테스트는 사용자 지침의 `rdev` 개발 pod를 사용한다. offload hook이 제공하는 명령을 따른다.
  로컬의 작은 소스 조사·stdlib 유한 검사는 무거운 Lean 빌드와 구별한다.
- 기존 회사 블로그, SW, Kuratowski 작업트리는 수정하지 않는다.

## 5. Continuous AI는 증명 계약 이후에 연결

공개 원격 저장소를 만들었고 결정적 CI를 구성했다. 최신 secret·workflow·pilot 상태는
[도입 기록](continuous-ai-adoption.md)을 따른다.
논문식 증명과 모듈 계약 없이 "계속 증명해라"를 예약하는 방식은 쓰지 않는다.

배포 순서:

1. M0의 검증 가능한 빌드와 최소 API를 만든다.
2. 작업 목록에는 **계약이 확정되고 의존성이 끝난 보조정리**만 ready로 둔다.
3. 작업자는 하나의 ready 작업을 구현하고 PR을 만든다. 열린 구현 PR은 초기 2개 이하로 제한한다.
4. 검사기는 compile/공리 감사/예정 선언과 실제 선언의 연결을 검증한다.
5. 메인은 정확한 PR head의 진술·가정·종이 증명과의 대응을 검토한다.
6. triage는 상태와 실패 원인을 갱신하고, planner는 완료된 작업 다음의 후보를 제안한다.

초기 주기 제안은 PR 현황 갱신 2시간, ready 작업 조사 6시간이다. 이벤트 기반 CI는 PR마다 실행한다.
입력 SHA·계약·실패 지문이 그대로면 모델을 다시 호출하지 않고, 완료 시 예약 작업을 중지한다.
이는 아직 배포된 주기가 아니다. 실제 사용량과 작업 수행 시간에 따라 조정한다.

### 모델과 인증의 경계

현재 대화의 Sol subagent 호출과 GitHub 예약 runner의 모델 호출은 다른 실행 경로다.
예약 구현 작업도 사용자 지정 Sol/xhigh를 유지하려면, 배포 시 그 모델을 실행할 runner와
인증·비용 경로를 확인해야 한다. 기존 Claude 구독 토큰이 Sol을 실행할 수 있다고 가정하지 않는다.
재사용 Kit의 보고/분류 기능과 증명 구현 runner를 구별한다. 이 부분은 M0 이후 운영 설계의 확인 항목이다.

호스팅 도구는 목적에 맞게 고른다. 기존 Claude Action 기반 시스템을 재사용하더라도
이를 gh-aw로 부르지 않는다. gh-aw 채택 자체를 수학 프로젝트의 완료 조건으로 삼지 않는다.
사용자는 공개 저장소 생성과 적절한 시점의 배포를 승인했다. 실제 실행과 구성은 도입 기록에서 추적한다.

## 6. 완료 판정

- 최종 상수와 정규성 정의를 읽고 의도한 수학과 일치함을 확인.
- 추가 수학 가정, `sorry`, `admit`, 새 공리, `native_decide` 없이 최종 정리까지 연결.
- 허용 공리는 `propext`, `Classical.choice`, `Quot.sound`; 선언 전체 감사 범위를 확인.
- 모든 프로젝트 Lean 파일이 루트 import와 빌드/감사에 포함됨을 확인.
- 종이 문서와 Lean 선언 사이의 가정·양화사·결론 일치 확인.
- 정확한 소스 SHA에서 build와 CI 성공을 기록. 유한 Python 검사는 별도의 회귀 증거로 표시.
- 그 전까지 README와 블로그에 "Lean으로 증명했다"고 쓰지 않는다.

## 7. 블로그와의 연결

글의 중심은 같은 소수 나열을 정수 접두사와 무한 소수로 바라보는 두 이야기다.
수학적 설명은 현재의 고전 정리만으로도 완결된다. 형식화 프로젝트가 완료되면
완성된 정리와 재현 가능한 저장소를 짧은 후기로 붙인다. 형식화 개발 일지 전체를 본문에 넣지 않는다.
