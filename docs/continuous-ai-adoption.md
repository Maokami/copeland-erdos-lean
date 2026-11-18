# Continuous AI 도입 설계

2026-11-18 현재 **수학 증명·공개 배포·CI 검증 완료, AI 인증 대기**다. 사용자는 최종 정규성 증명과 적절한 시점의
Continuous AI 배포를 승인했다. 공개 원격 저장소는 생성했으며 예약 workflow는 아직 없다.
저장소: https://github.com/Maokami/copeland-erdos-lean .
사용자는 공개 저장소를 선택했다. 소스 게시와 GitHub CI 검증을 완료했다. AI pilot은 아직 실행하지 않았다.
새 저장소의 Actions secret 목록이 비어 있음을 확인했고 구독 토큰 등록을 요청했다.

## 관찰한 상태와 첫 적용 범위

수학 구현 커밋은 `1e4d34163b388ab533a80f6573dbadf46ad0b114`다.
메인이 pod에서 전체 빌드, 새 공리 감사, 공개 예제를 직접 재실행했고
23개 라이브러리와 루트의 472개 선언을 확인했다. 최초 scaffold만 있던 시점의
Kit inventory는 현재 입력으로 사용하지 않고, 이 커밋에서 다시 선택한다.

반복되는 작업은 수학 계약과 실제 선언의 차이 확인, 미완성 의존성 파악,
새 구현의 빌드·공리 감사다. 컴파일과 import 누락은 결정적 CI가 처리하고,
수학적 가정의 적절성이나 재사용 가능한 보조정리 선택은 메인이 검토한다.

첫 배포는 다음 순서로 진행한다.

1. GitHub-hosted Linux에서 정확한 Lean/Mathlib pin을 사용하는 결정적 CI.
   `scripts/check_lean_inventory.py`, `scripts/check_combinatorics.py`, `lake build`,
   `lake env lean CopelandErdosAudit.lean`을 실행한다. 마지막 명령은 캐시와 별도로 감사를 재실행한다.
2. 공개 Kit의 검토된 전체 SHA에 고정한 Lean source-scan을 수동 시험한다.
   `CopelandErdos/**/*.lean`, `docs/proof.md`, 구현 계획을 근거로 선언·가정·문서 불일치를
   최대 세 개 제안하며, 유효한 빈 결과도 허용한다. 실제 선택 파일은 generator 출력으로 검토한다.
3. 같은 입력 배치의 재실행에서 중복 보고와 불필요한 모델 호출이 없는지 확인한다.
   현재 정규성 목표는 완료됐으므로 신규 수학 연구를 6시간마다 시작하는 schedule은 활성화하지 않는다.
   먼저 수동 유지보수 검토를 평가하고 입력 변경에 따른 후속 조사의 유용성을 확인한다.
4. 구현 PR이 생기면 실제 required check 이름을 확인하고 PR triage를 추가한다.

## 제안과 구현의 구분

기존 `continuous-ai-kit`은 source scan과 PR triage를 제공한다.
현재 Kit 자체는 소스 수정, 증명 구현, PR 생성 또는 병합을 수행하지 않는다.
이를 설치한 사실을 “수학 연구가 자율적으로 구현된다”고 보고하지 않는다.

증명 구현은 사용자 지정 `gpt-6.1-sol` / `xhigh`를 유지한다.
이 대화의 subagent 실행과 GitHub 예약 실행은 별개다. 예약 writer를 연결하려면
해당 모델을 실행할 인증·runner 경로를 확인해야 한다. Claude OAuth 토큰으로
Sol을 실행할 수 있다고 가정하지 않고, API 과금 경로로 임의 전환하지 않는다.

자동 구현 후보는 메인이 정리의 양화사·가정·결론과 허용 파일을 확정하고 의존성이
완료된 작업만 대상으로 한다. 후보 제안은 승인이나 실행 지시가 아니다.
초기 구현 동시성은 한 작업으로 제한하고, 계약 변경과 새 수학 가정은 자동으로 허용하지 않는다.

## 검증과 운영 경계

- Lean 컴파일은 해당 형식 명제의 검증이다. 자연어 목표와의 일치는 별도 검토한다.
- source scan의 인용·출력 스키마 검증은 수학적 정확성 검증이 아니다.
- Kit 보고/분류의 Claude 인증은 이름으로만 참조하고 secret 값은 파일·로그에 남기지 않는다.
- source SHA, Kit SHA, run URL, 출력, 중복 여부, 승인/기각을 실제 pilot 뒤 기록한다.
- 동일 입력의 중복, 반복 실패 또는 정규성 목표 완료 시 신규 조사 schedule을 중지한다.
- 첫 pilot의 실행 시간·모델 사용량·유용한 결과 수는 아직 측정하지 않았다.

현재 AI 모델 실행은 새 저장소의 구독 토큰 등록을 기다리고 있다.
공개 CI와 소스 배포는 이 인증 단계와 독립적으로 진행한다.

## 구성 파일 검증

- Kit pin: `0444e53db6e9fa5dc9a750f40bd08a91fd0bcd5c` (공개 원격 커밋 확인).
- Caller: `.github/workflows/continuous-ai-proof-review.yml`.
- Config/prompt: `.github/continuous-ai/proof-review.json`, `.md`.
- 선택: 라이브러리 23개 파일, 138,986 bytes, 4개 배치(6/6/6/5).
- Policy: AGENTS, 종이 증명, 구현 계획. source coverage 목록에서는 제외한다.
- 모델: Kit 기본 `claude-sonnet-5-5`, max-turns 12, 후보 최대 3개.
- 범위: 완료된 정리의 명세 대응과 구체적인 재사용 개선 후보만 보고한다.
- 현재 트리거: **main의 수동 dispatch만**. schedule 없음, recovery_only=false.
- Kit generator/동일 config validator, 전체 workflow actionlint, diff 검사를 통과했다.
- 메인은 caller의 권한·핀·트리거, prompt 계약, Kit 검증/게시 경로를 검토했다.
  Kit 전체 코드의 새 독립 감사나 현재 저장소의 live pilot을 했다는 뜻은 아니다.
- Secret이 등록되면 batch 0 수동 pilot과 동일 batch/digest 재실행을 검증한다.

최종 정규성 목표는 완료됐으므로 미완성 증명을 계속 시도하는 자동 writer는 배포하지 않는다.
유지보수 검토의 유용성을 확인하기 전 신규 조사 schedule도 활성화하지 않는다.

## 공개 배포 검증

- 공개 저장소: https://github.com/Maokami/copeland-erdos-lean .
- 게시 커밋: `ae126fe34c79a730d8b33cc29c58cbc70acbfe68`.
- 첫 GitHub CI: [44265383894](https://github.com/Maokami/copeland-erdos-lean/actions/runs/44265383894), **success**.
- `Lean CI`에서 Python 검사, Lean 빌드, 새 공리 감사, 공개 최종 정리 예제 모두 통과했다.
- GitHub에 CI와 수동 `Continuous AI (proof-review)` workflow가 active 상태로 등록됨을 확인했다.
  active 등록은 AI 모델 실행 성공을 뜻하지 않는다.
- 최초 HTTPS push는 기존 OAuth 자격의 workflow scope 부족으로 거절됐고,
  이미 구성된 SSH 인증으로 같은 저장소에 게시했다. 권한 정책을 변경하지 않았다.
- 마지막으로 확인한 Actions secret 목록은 비어 있다. `CLAUDE_CODE_OAUTH_TOKEN` 등록은 사용자에게 요청했으며,
  값은 읽거나 기록하지 않았다. 따라서 실제 AI 실행·검증·게시와 동일 입력 no-op 관찰은 아직 없다.
- 현재 scheduler와 자동 writer는 없다. 검증된 정리를 유지하며 수동 검토 pilot부터 평가한다.

구독 인증 절차는 [Anthropic 공식 설정 문서](https://code.claude.com/docs/en/github-actions),
사용 모델 ID는 [공식 Sonnet 5.5 문서](https://platform.claude.com/docs/en/models/sonnet-5-5/overview)에서 확인했다.
후속 문서 기록 커밋은 수학 소스와 workflow를 바꾸지 않는다.
