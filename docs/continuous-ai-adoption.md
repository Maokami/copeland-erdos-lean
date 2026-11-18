# Continuous AI 도입 설계

2026-11-18 현재 **설계 단계**다. 사용자는 최종 정규성 증명과 적절한 시점의
Continuous AI 배포를 승인했다. 공개 원격 저장소는 생성했으며 예약 workflow는 아직 없다.
저장소: https://github.com/Maokami/copeland-erdos-lean .
사용자는 공개 저장소를 선택했다. 소스 게시·CI·AI pilot은 아직 실행하지 않았다.
새 저장소의 Actions secret 목록이 비어 있음을 확인했고 구독 토큰 등록을 요청했다.

## 관찰한 상태와 첫 적용 범위

로컬 main의 최초 scaffold HEAD는 `36dc68a575cc9af01b6d43dce09257a9ab72a3df`다.
M1/M2 구현과 문서는 미커밋 상태이므로 Kit의 committed-source inventory는
현재 작업 파일 전체를 나타내지 않는다. 검증된 구현을 보존해 커밋한 뒤
정확한 SHA에서 입력 목록을 다시 확인해야 한다.

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
   유용한 결과가 확인된 뒤 신규 조사 주기를 설정한다. 초기 제안은 6시간이며 아직 활성화하지 않았다.
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

현재 배포를 보류하는 이유는 수학 정리 전체의 완료를 기다리기 때문이 아니라,
검증된 입력 revision과 인증 경로를 먼저 확정해야 하기 때문이다.
