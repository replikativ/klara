#!/bin/sh
set -eu
mkdir -p target/jvm-modes/classes
javac -d target/jvm-modes/classes experiments/interpreter/jvm_modes/LoopModes.java
for process in 0 1 2; do
  java -Xmx256m -Xint -XX:CompileCommand=dontinline,LoopModes::plain -XX:CompileCommand=dontinline,LoopModes::checked -cp target/jvm-modes/classes LoopModes int 10000 20 > "target/jvm-modes/int-$process.tsv"
  java -Xmx256m -XX:-UseJVMCICompiler -XX:-TieredCompilation -Xbatch -XX:+UnlockDiagnosticVMOptions -XX:+LogCompilation "-XX:LogFile=target/jvm-modes/c2-$process.xml" -XX:CompileCommand=dontinline,LoopModes::plain -XX:CompileCommand=dontinline,LoopModes::checked -cp target/jvm-modes/classes LoopModes c2 10000 20000 > "target/jvm-modes/c2-$process.tsv"
done
