#!/bin/bash

create_data_from_program() {
    program=${@:1:$#-1}
    file=${@: -1}
    echo "Program: " $program
    echo "File: " $file
    rm $file
    touch $file
    for i in {1..17}
    do
        input_vector=""
        power_i=$((2 ** $i))
        for _ in $( eval echo {1..$power_i})
        do
            input_vector+=" $RANDOM"
        done
        START="$(date +%s%N)"
        $program ${input_vector}
        DURATION=$(( $(date +%s%N) - START ))
        echo $power_i $DURATION >> "$file"
    done
}

create_data_tree_building() {
    program=${@:1:$#-1}
    file=${@: -1}
    echo "Program: " $program
    echo "File: " $file
    rm $file
    touch $file
    for i in {8..8}
    do
        input_vector=""
        power_i=$((2 ** $i))
        for _ in $( eval echo {1..$power_i})
        do
            input_vector+=" $RANDOM"
        done
        $program ${input_vector}
        rr replay
        echo $power_i $(cat tree_building_ns.txt) >> "$file"
    done
}
