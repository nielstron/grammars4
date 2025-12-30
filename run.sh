while true; do
   git add .
   git commit -m "iter"
   codex  --search exec -s workspace-write "i translated some of the proofs in src/Grammars/Classes/ContextFree/ClosureProperties/Union.lean to lean 4. translate the remainder to lean 4 as well. start with the first failing single proof, resolve issues one by one and then iterate until the proof works. after every change check the output of 'lean build src/Grammars/Classes/ContextFree/ClosureProperties/Union.lean' then proceed to the next one. I have to go to a doctor's appointment so I can't hang around and approve stuff. When I come back, it will be so good if all of this is done, complete with a markdown  report of any issues. it might help to comment out later proofs when working on the first ones in a file, but make sure to uncomment everything when completing. keep your progress up to date in PORTING_REPORT.md. When done proceed to the next proof file whose dependencies have been translated. feel free to check the git history, anything not named 'iter' for how I translated things before."
   sleep 30
done
