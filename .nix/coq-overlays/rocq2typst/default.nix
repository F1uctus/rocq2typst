{
  lib,
  mkCoqDerivation,
  coq,
  coq-elpi,
  version ? ../../../.,
}:

mkCoqDerivation {
  pname = "rocq2typst";
  opam-name = "rocq2typst";
  inherit version;
  useDune = true;

  propagatedBuildInputs = [ coq-elpi ];

  meta = {
    description = "Rendering of Rocq statements as Typst mathematical markup";
    license = lib.licenses.gpl3Plus;
  };
}
