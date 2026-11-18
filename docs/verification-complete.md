# 최종 정규성 검증 기록

2026-11-18. 수학 설계·계약·전체 연결의 검토는 메인 Astra,
구현은 사용자 지정 `gpt-6.1-sol` / `xhigh` 작업자들이 수행했다.

## 최종 계약과 의미 검토

`Normality.copelandErdos_normal : NormalInBase 10 copelandErdos`.
상수는 실제 소수의 표준 십진 전개를 이어 붙인 스트림의 `Real.ofDigits`다.
`NormalInBase`는 [0,1) 범위와 표준 `Real.digits`의 모든 비어 있지 않은 패턴 빈도 수렴을 요구한다.
분모는 전체 접두사 길이이며 겹치는 출현과 소수 중간에서 끝나는 모든 접두사를 포함한다.

메인은 예외 집합의 양화 순서(K가 cutoff와 길이에 독립), 표준 전개의 단사성,
list/finset 변환의 중복 보존, 소수 cutoff의 inclusive/exclusive 차이,
경계에서 모든 접두사로의 이전, 실제 실수의 floor/자리 복원을 소스와 대조했다.
중간 generic criterion의 가정은 최종 소수 적용에서 모두 증명해 제거했다.
새 소수정리나 소수 숫자의 독립성 가정은 사용하지 않는다.
정수 로그 형태의 계수 상계를 직접 사용하므로 실수 로그 Big-O 선언 자체는 별도 제공하지 않는다.

## 메인의 직접 재실행

작업자들의 단독 모듈 빌드·private-inclusive 감사 이후 메인이 실행했다.

```sh
python3 -I scripts/check_lean_inventory.py
python3 -I scripts/check_combinatorics.py
rdev x bertha-ultra --task ce-geometric -- lake build
# 동일한 동기화 pod mirror에서 별도로 새로 실행:
lake env lean CopelandErdosAudit.lean
lake env lean examples/Normality.lean
```

직접 관찰한 exit 0 결과:

```text
Lean inventory passed: 23 library source(s), root and audit connected
Axiom audit passed: 24 modules, 472 declarations; axioms: [Quot.sound, Classical.choice, propext]
Build completed successfully (2895 jobs).
```

감사는 root와 각 source를 직접 `import all`로 읽어 비공개/생성 선언을 포함한다.
472는 정리의 개수가 아니다. 새로 실행한 감사에서도 같은 결과였다.
공개 예제의 `#print axioms`에서 최종 normality와 펼친 빈도 정리 모두
`propext`, `Classical.choice`, `Quot.sound`만 출력됐다.
M0에서 감사의 비공개 custom-axiom 음성 검사를 이미 수행했다.

Python 회귀 결과: occurrence/residue 7,650건, append 53,790건,
유리수 4차 모멘트 36건, 십진 roundtrip 0..1000 및 prefix 235711 통과.
이는 Lean 일반 증명과 별도의 유한 검사다. CI actionlint와 git diff 검사는 통과했다.

## 입력과 출처

Lean v4.35.0 / Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
메인 재실행 pod snapshot `848e31a23f78929d31be8528d4d2535640c196f2`,
tree `2c232a4ec108b8d7101faad6706fea8150edb4c1`.
이것은 rdev 검증 snapshot이며 공개 GitHub 커밋과 다르다. 문서 완료 갱신은 이후다.
모든 무거운 Lean 실행은 Linux pod에서 수행했다.
초기 작업자 일부의 공유 package symlink에서 산출물 경합이 발생해 각 작업의 독립적인
Linux package 복사본으로 바꾼 뒤 최종 검증했다. Mac package는 APFS clone을 유지했다.

최종 소스 SHA256:

```text
7201734276432e57400f30b86b19740db352b271653f92602ef346c2b2a3e9c5  CopelandErdos.lean
befcdc2e0ae7d2ed97a66a63e2776dc51331bd88c517eac382ae604c63ea97b9  CopelandErdosAudit.lean
d22525373c59a7e983cbdf71a0c91f61cafd9f46f5059bfda420c8cda9a993b8  CopelandErdos/Analysis/GeometricBounds.lean
519b6e77af5aa386f1ab07c17bb61fdf680de24de4e1dba1165e997d1cd56c68  CopelandErdos/Digits/BlockStream.lean
12e639a8a8ca1b2859b88005a3d27237ca0087d007fb7cb08f4ba2f368088a13  CopelandErdos/Digits/NatWord.lean
6f2f3273e2b689b820ef78aabeb3297a8291f897a49e2647609072d45eda3eb4  CopelandErdos/Digits/PrimeStream.lean
185acd6cdedaf55dd4dfd376af4423677961c3b0ce9100fb234d28eb771080ed  CopelandErdos/Digits/RealExpansion.lean
2394dbe23a581270ba9c33812635c6fb24372b6749e7daedd10c8f45fd7e2b03  CopelandErdos/Normality/BoundaryCriterion.lean
054324e53bb7c4bf4f006e6e5e0381cff1656ac33def38ddc37cb39fece3bcb6  CopelandErdos/Normality/NormalDigits.lean
383099cc20692f962bbd6b564478a3aef896a7beded95770d3ae65a67b6bbb5d  CopelandErdos/Normality/PrefixTransfer.lean
8e86dfd48a4bbc1b36b988643b35145224f941deb02a9133aba89f8d38f0829f  CopelandErdos/Normality/PrimeConcatenation.lean
f8b562465f797039f4ad6a8b7a757dfb2e9ed844528e3e8c458ba0bb9bc26638  CopelandErdos/Normality/RealBridge.lean
49f56d6d8085fe980779f4c739e9c51340109734b417c93b5aa7c61da477180a  CopelandErdos/NumberTheory/BadIntegerCounting.lean
382cbeaa0762f38df62517d635d4668e3120c9ea45649e2994bdc3be5734bb26  CopelandErdos/NumberTheory/BadIntegers.lean
d5f6dc09ffd6affcd3d5e94103e2e08ddaaaf8bc0a141f7abe6c8a055a2f684b  CopelandErdos/NumberTheory/BadPrimeMass.lean
f8dbb20f6f01a5984ffaebf49d62d4a551ee8d2d8d755b5f552bc9297ed8ca68  CopelandErdos/NumberTheory/PrimeBounds.lean
5ef10059495be428e257f4e07c35aa755c7659fdb0e697c268a500d9314f0d2d  CopelandErdos/NumberTheory/PrimeDigitMass.lean
9cfc34f9a24c4203d44a0d3dac84b3f612db02a6119766c6f2777af96da653c7  CopelandErdos/NumberTheory/PrimePrefixBounds.lean
e1fb546b7f14ca270bc29d07138883fc05b7ffcf911e5d56e9944dc61b2e3eb7  CopelandErdos/Probability/FiniteMoments.lean
32a14381d5bfad2c2d935226612c80b9a7bedb56aa1b986ac3c17cc92432f526  CopelandErdos/Words/BadWordArithmetic.lean
2080eb5c93f03e5ec091d1e678818a710e3df60ce999861d90cfcde11d190a97  CopelandErdos/Words/BadWords.lean
964af96be693b246513f54f4cd3b66ba946c5a4ab98897be3d7092e9298834ff  CopelandErdos/Words/BlockCounts.lean
647405509bab7bd40b0490b5678896bdcdb2f24ba9635e5a677c9cf3c1377967  CopelandErdos/Words/Concatenation.lean
33d23743cca0448a4356d1ce24a85a19c810d8bd655387484177aae1fecba831  CopelandErdos/Words/Occurrences.lean
fbaa1f73326fc8af35ee0650bab4e4d045181a6bfb243f7da224b160d5c24332  CopelandErdos/Words/UniformBlocks.lean
85534b1e9fd261a0956faabb8943085f9c52ac375ca6a726db0552edc0dfe318  examples/Normality.lean
de654f7cfea120bdf80963f361ce5706e45ee49e7e8dd091b0ec52193c387030  .github/workflows/ci.yml
```

## 공개 배포와의 구분

위 기록은 실제 소스 검토와 pod에서 실행한 검증이다.
GitHub CI 및 Continuous AI pilot의 run URL/실행 결과는
[별도 도입 기록](continuous-ai-adoption.md)에 남긴다.
이번 정규성 구현을 예약 Continuous AI가 자율적으로 완성했다고 주장하지 않는다.
