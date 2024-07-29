from lean_dojo import LeanGitRepo, trace

repo = LeanGitRepo("https://github.com/yangky11/lean4-example", "a61b40b90afba0ee5a3357665a86f7d0bb57461d")
trace(repo, dst_dir="traced_lean4-example")