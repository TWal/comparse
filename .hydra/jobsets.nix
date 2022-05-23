{src}:

let
  pkgs = import <nixpkgs>;
  makeJob = priority: description: flake: {
    inherit description flake;
    enabled = 1;
    type = 1;
    hidden = false;
    checkinterval = 60;
    schedulingshares = priority;
    enableemail = false;
    emailoverride = "";
    keepnr = 1;
  };
in

{
  jobsets = pkgs.writeText "spec.json" (builtins.toJSON {
    main = {
      name = "main";
      value = makeJob 1000 "main branch" "github:TWal/comparse?ref=${src.rev}";
    };
  });
}
