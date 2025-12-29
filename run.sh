while true; do
   git add .
   git commit -m "iter"
   codex  --search exec -s workspace-write "i translated some of the files to lean 4 proofs (check out contextfree/basics/toolbox). translate the remainder to lean 4 as well. start with  a single proof, fix the syntax and then iterate until the proof works. then proceed to the next one. I have to go to a doctor's appointment so I can't hang around and approve stuff. When I come back, it will be so good if all of this is done, complete with a markdown  report of any issues. start with the simple proofs with few dependencies and gradually work your way towards the more complex proofs. it might help to comment out later proofs when working on the first ones in a file, but make sure to uncomment everything when completing. keep your progress up to date in PORTING_REPORT.md." 
   sleep 1
done
