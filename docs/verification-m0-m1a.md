# M0·M1a 검증 기록

날짜: 2026-11-17. 구현 작업자: `gpt-6.1-sol` / `xhigh`.
메인 Astra는 정리 계약·소스를 검토하고 최종 빌드와 로컬 import 목록 검사를 다시 실행했다.

## 완료 범위

- Lean v4.35.0 및 Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 고정.
- `CopelandErdos.Words.OccursAt`, `occurrenceCount`와 의미 대응 정리.
- 빈 host·빈 패턴·짧은 host, 전체 길이 상계.
- append 시 두 계수 합의 하한과 추가 `k−1` 상한.
- append 길이 t에 따른 증가량 t 상계.
- kernel `decide` 예제 5개: 겹침, 짧은 host, 빈 host, 빈 패턴, 경계를 넘는 출현.
- 전체 라이브러리 import 목록과 비공개 선언을 포함한 공리 감사.

주요 검토 사항: `OccursAt`의 길이 조건이 완전히 포함된 출현만 허용한다.
`occurrenceCount_eq_card`는 `w≠[]`에서 유효 시작점의 개수와 일치하고,
`occursAt_start_lt`는 실제 출현 위치가 집계 범위에서 빠지지 않음을 보인다.
상한을 위해 결론이나 독립성 가정을 추가하지 않았다.

## 실제 실행

작업자와 메인의 최종 명령:

```sh
python3 -I scripts/check_lean_inventory.py
lake build
```

메인이 직접 관찰한 최종 결과(exit 0):

```text
Lean inventory passed: 1 library source(s), root and audit connected
Axiom audit passed: 2 modules, 53 declarations; axioms: [Quot.sound, Classical.choice, propext]
Build completed successfully (799 jobs).
```

메인 재실행에서 이미 빌드된 감사 결과는 `Replayed`로 표시됐다.
53개는 공개 정리 수가 아니라 비공개 보조정리·예제와 생성된 선언을 포함한 감사 대상 선언 수다.
799 jobs 역시 새로 증명한 정리 수가 아니다. Mathlib 의존성과 캐시된 작업을 포함한다.

## 감사의 실패 경로

작업자가 임시 소스에 private custom axiom `auditCoverageProbe`와 그것을 쓰는
private theorem `auditCoverageProbeUse`를 삽입했다. 감사는 **두 선언을 이름과 함께 거부했고
exit 1**이었다. 임시 삽입을 복구한 뒤 전체 빌드와 감사가 다시 통과했다.
이 음성 검사는 작업자가 실행한 결과이며 메인이 같은 삽입을 반복하지는 않았다.
최종 로컬 소스 해시가 작업자가 검증한 복구 후 소스 해시와 일치함은 메인이 직접 확인했다.

이 과정에서 Lean 4.35의 일반 import만으로는 비공개 선언까지 감사했다고 말할 수 없음을 확인했다.
감사 파일은 루트와 각 라이브러리 소스를 **직접 `import all`**한다.
`scripts/check_lean_inventory.py`는 이 import-all 목록과 실제 파일 목록도 대조한다.

## 소스 provenance

메인이 확인한 최종 Lean 소스 SHA256:

```text
6a01acc4dbb31bcdaa242e9cb164e80446d279257e4982d68a422eb009f50468  CopelandErdos.lean
33d23743cca0448a4356d1ce24a85a19c810d8bd655387484177aae1fecba831  CopelandErdos/Words/Occurrences.lean
b58063465db977697d6f386009ff209d71366e5185bfc2552aa62c246148fbe9  CopelandErdosAudit.lean
```

로컬 초기 scaffold commit은 `36dc68a`다. 이번 구현은 이 기록 시점에 미커밋 변경이며
원격 GitHub 저장소 생성·게시·Continuous AI 배포는 하지 않았다.

## 남은 범위

M1b(4차 모멘트), M1c(소수 계수 하한 wrapper), 나쁜 단어 상계, 무한 스트림,
모든 접두사의 극한, 실수 자리 전개와의 일치는 아직 구현하지 않았다.
따라서 이 결과는 **Copeland–Erdős 정규성의 완성된 Lean 증명**이 아니다.
