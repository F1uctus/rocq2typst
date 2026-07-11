{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  attribute = "rocq2typst";
  no-rocq-yet = true;

  default-bundle = "rocq-9.1";

  bundles = {
    "rocq-9.1" = {
      rocqPackages = {
        rocq-core.override.version = "9.1";
      };
      coqPackages = {
        coq.override.version = "9.1";
        stdlib.job = true;
        bignums.job = true;
        rocq2typst = { main-job = true; };
        rocq2typst-mathcomp.job = true;
        rocq2typst-analysis.job = true;
        rocq2typst-coqeal.job = true;
        rocq2typst-infotheo.job = true;
      };
      push-branches = [ "main" ];
    };
  };

  cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community = {};
}
