if [ -z "$1" ]; then
    echo "usage: $0 [day]"
    exit
fi
DAY=`printf %02d "$1"`
solns/$DAY.pl <inputs/$DAY.txt
