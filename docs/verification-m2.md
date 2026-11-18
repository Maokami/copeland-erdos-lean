# M2 통합 검증 기록

날짜: 2026-11-18. 메인 Astra가 수학적 계약과 소스를 검토했고,
사용자가 지정한 `gpt-6.1-sol` / `xhigh` 작업자들이 파일별로 구현했다.

## 증명 범위

M2a의 `Words.exists_badWords_card_le`:
진법 b≥2, 길이 k≥1인 패턴 w, ε>0에 대해 양의 K가 존재하고 모든 ℓ≥1에서
`#{u : |C_w(u)/ℓ − b^(−k)| > ε} ≤ K*b^ℓ/ℓ²`.
C는 기존의 겹치는 출현 계수이며 선행 0을 포함한 모든 단어를 센다.

시작 위치를 mod k로 분할하고 단사 좌표 제한의 평균 보존을 증명했다.
그룹 편차의 4차 모멘트는 실제 전체 단어 공간에서 `3m_r²≤3ℓ²`로 제한된다.
문턱 `εℓ/(2k)`에 Markov와 합집합 상계를 적용하여 충분히 큰 길이에서
`48k⁵/ε⁴`를 얻고, 작은 길이는 K에 흡수한다. 최적 상수는 목표가 아니다.
독립성이나 계수 상계를 미증명 가정으로 남기지 않았고 소수 숫자의 독립성을 가정하지 않는다.

M2b는 실제 `Nat.nth Nat.Prime`의 역순 `Nat.digits`로 표준 숫자 블록을 만들었다.
각 블록의 양의 길이, 선행 0 없음, 원래 소수 복원, 누적 길이 증가,
각 위치의 유일한 블록 소속을 증명했다. 실제 무한 `primeDigits`와 유한 flatten이
정확히 일치하며 십진 스트림의 처음 여섯 자리가 `235711`임을 Lean으로 확인했다.

## 메인의 통합 검증

로컬 inventory: `9 library source(s), root and audit connected`.
루트는 모든 라이브러리를 공개 import하며 감사는 각 파일을 직접 `import all`로 읽는다.

전체 통합 빌드를 `lake build`로 재실행했다.

메인이 직접 관찰한 exit 0 출력:

```text
Replayed CopelandErdosAudit
Axiom audit passed: 10 modules, 243 declarations; axioms: [Quot.sound, Classical.choice, propext]
Build completed successfully (2880 jobs).
```

243은 비공개·생성 선언을 포함한 감사 대상 수이며 새 정리의 개수가 아니다.
2880 jobs는 의존성과 캐시를 포함한다. 감사의 음성 검사는 M0에서 이미 확인했다.
작업자들의 개별 빌드·감사 보고에 더하여 메인이 전체 통합 빌드를 재실행했다.
기존 Python 유한 검사는 이번에 재실행하지 않았으며 위 결과는 Lean 증명 검증이다.

## 재현 입력

Lean v4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 유지.
메인이 검증한 소스와 최종 소스의 SHA256 일치를 확인했다.
아래는 최종 로컬 Lean 소스 전체의 SHA256이다.

```text
fbe2eb022e6d776ce1f69552052bd397fc11eb2dfd992d2cd37436c37effd41f  CopelandErdos.lean
429ea3664e183fb1c208cdabdcb65a54a20975ccc2e8f199d6e1a0454587fc64  CopelandErdosAudit.lean
519b6e77af5aa386f1ab07c17bb61fdf680de24de4e1dba1165e997d1cd56c68  CopelandErdos/Digits/BlockStream.lean
6f2f3273e2b689b820ef78aabeb3297a8291f897a49e2647609072d45eda3eb4  CopelandErdos/Digits/PrimeStream.lean
f8dbb20f6f01a5984ffaebf49d62d4a551ee8d2d8d755b5f552bc9297ed8ca68  CopelandErdos/NumberTheory/PrimeBounds.lean
e1fb546b7f14ca270bc29d07138883fc05b7ffcf911e5d56e9944dc61b2e3eb7  CopelandErdos/Probability/FiniteMoments.lean
32a14381d5bfad2c2d935226612c80b9a7bedb56aa1b986ac3c17cc92432f526  CopelandErdos/Words/BadWordArithmetic.lean
2080eb5c93f03e5ec091d1e678818a710e3df60ce999861d90cfcde11d190a97  CopelandErdos/Words/BadWords.lean
964af96be693b246513f54f4cd3b66ba946c5a4ab98897be3d7092e9298834ff  CopelandErdos/Words/BlockCounts.lean
33d23743cca0448a4356d1ce24a85a19c810d8bd655387484177aae1fecba831  CopelandErdos/Words/Occurrences.lean
fbaa1f73326fc8af35ee0650bab4e4d045181a6bfb243f7da224b160d5c24332  CopelandErdos/Words/UniformBlocks.lean
```

## 남은 범위

M3의 예외 정수 개수 상계, 전체 소수 자릿수 하한과 경계 오차, 모든 접두사 수렴을
아직 구현하지 않았다. M4의 실제 실수 자리 전개 연결도 남아 있다.
따라서 전체 Copeland–Erdős 정규성의 형식화는 아직 완료되지 않았다.
원격 저장소 게시와 Continuous AI 예약 배포도 아직 수행하지 않았다.
