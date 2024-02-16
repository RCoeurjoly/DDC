#!/bin/sh

DATADIR="$(pwd)/.mysql"
SOCKET="$DATADIR/mysql.sock"

echo $DATADIR

alias query="mysql --socket=$SOCKET --user=root --password=$MYSQL_ROOT_PASSWORD"

resetDB() {
    echo "Resetting DB"
    rm -rf $DATADIR
    mkdir $DATADIR

    mysqld \
        --user="$MYSQL_USER" \
        --datadir=$DATADIR \
        --initialize-insecure

    echo "Waiting for DB startup"
    mysqld \
        --datadir=$DATADIR \
        --socket=$SOCKET \
        --bind-address="$MYSQL_HOST" &

    local i
    for i in {30..0}; do
        if mysql --socket=$SOCKET --user=root <<< 'SELECT 1' &> /dev/null; then
            break
        fi
        sleep 1
    done
    if [ "$i" = 0 ]; then
        echo "Unable to start server."
        exit
    fi

    echo "Altering root password"
    mysql --socket=$SOCKET --user=root \
        <<< "ALTER USER 'root'@'localhost' IDENTIFIED BY '${MYSQL_ROOT_PASSWORD}' ;"

    stopDB
}

startDB()
{
    echo "Waiting for DB startup"
    mysqld \
        --datadir=$DATADIR \
        --socket=$SOCKET \
        --bind-address="$MYSQL_HOST" &

    local i
    for i in {30..0}; do
        if query <<< 'SELECT 1' &> /dev/null; then
            break
        fi
        sleep 1
    done
    if [ "$i" = 0 ]; then
        echo "Unable to start server."
        exit
    fi

    if [ $MYSQL_ONLY_FULL_GROUP_BY ]; then
        echo "Disabling ONLY_FULL_GROUP_BY setting"
        query <<< "SET GLOBAL sql_mode=(SELECT REPLACE(@@sql_mode, 'ONLY_FULL_GROUP_BY', ''))"
    fi
}

stopDB()
{
    mysqladmin --socket=$SOCKET --user=root shutdown --password=$MYSQL_ROOT_PASSWORD
}

initDB() {
    echo "Initializing DB"

    echo "Creating database"
    query <<< "CREATE DATABASE IF NOT EXISTS \`$MYSQL_DATABASE\` CHARACTER SET \`utf8\` COLLATE \`utf8_general_ci\` ;"
    query <<< "CREATE DATABASE IF NOT EXISTS \`$MYSQL_TEST_DATABASE\` CHARACTER SET \`utf8\` COLLATE \`utf8_general_ci\`;"

    echo "Creating user"
    query <<< "CREATE USER '$MYSQL_USER'@'%' IDENTIFIED BY '$MYSQL_PASSWORD' ;"

    query <<< "GRANT ALL ON \`$MYSQL_DATABASE\`.* TO '$MYSQL_USER'@'%' ;"
    query <<< "GRANT ALL ON \`$MYSQL_TEST_DATABASE\`.* TO '$MYSQL_USER'@'%' ;"

    query <<< "FLUSH PRIVILEGES;"

}

case "$1" in
    reset)
        stopDB
        resetDB
        startDB
        initDB
        ;;
    init)
        resetDB
        startDB
        initDB
        ;;

    start)
        if [ -e $DATADIR ]; then
            startDB
        else
            resetDB
            startDB
            initDB
        fi
        ;;

    stop)
        stopDB
        ;;
esac
