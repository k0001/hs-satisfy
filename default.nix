{ mkDerivation, base, constraints, kind-integer, kind-rational, lib, singletons
, singletons-base }:
mkDerivation {
  pname = "satisfy";
  version = "0.1";
  src = lib.sources.cleanSource ./.;
  libraryHaskellDepends =
    [ base constraints kind-integer kind-rational singletons singletons-base ];
  testHaskellDepends = [ base ];
  homepage = "https://gitlab.com/k0001/hs-satisfy";
  description = "Term-level satisfaction of type-level predicates";
  license = lib.licenses.asl20;
}
