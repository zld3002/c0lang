for i in 2048
#1 2 4 8 16 32 64 128 256 512 1024
do
    echo "== $i ============"
    echo "val SIZE = $i;" > tmp
    time cat tmp transitive.sml  | sml > /dev/null
done
rm tmp