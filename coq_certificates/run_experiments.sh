#!/bin/bash

# Delete previous experiment's auxiliary files and nia cache files
rm -rf .*.aux
rm -rf .nia.cache
rm -rf *.glob
rm -rf *.vo
rm -rf *.vok
rm -rf *.vos


BLUE='\033[1;34m'
PURPLE='\033[1;35m'
RED='\033[1;31m'
GREEN='\033[1;32m'
NC='\033[0m'

FILES="$HOME/Documents/wanda/coq_certificates/*.v"
fail=0
timeout=0
success=0
total=0

for f in $FILES
do
    ext=${f: -2}
    if [ $ext == ".v" ]
    then
    total=$((total+1))
    echo "Compiling proof script: $f"
    timeout 60s time coqc $f

    err=$?

    if [ $err == "0" ]
    then
        success=$((success+1))
        printf "${GREEN}success${NC}\n"
    else
        if [ $err == "1" ]
        then
            fail=$((fail+1))
            printf "${RED}fail${NC}\n"
            else
                if [ $err == "124" ]
                then
                    timeout=$((timeout+1))
                    printf "${PURPLE}timeout${NC}\n"
            fi
        fi
    fi
    fi
done

echo "Results"
echo "------------------------------------------------------------------------"
printf "${GREEN}Success:${NC} $success\n"
printf "${RED}Fail:${NC} $fail\n"
printf "${PURPLE}Timeout:${NC} $timeout\n"
printf "${BLUE}Total:${NC} $total\n"
echo "------------------------------------------------------------------------"
