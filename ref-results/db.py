# -*- coding: utf-8 -*-

import hashlib
import os.path
import sqlite3


## TODO: The domain_name and problem_name are currently not really
##       useful. We might at least warn on a query/update where these
##       don't match what is stored in the DB. I'm keeping them in
##       anyway for now so that they're available for debugging.


def _get_db_connection():
    dirname = os.path.dirname(os.path.abspath(__file__))
    dbfile = os.path.join(dirname, "ref-results.db")
    conn = sqlite3.connect(dbfile)
    ## TODO: It's probably not a good idea to create a new table
    ##       silently. If the table doesn't exist yet, that's
    ##       interesting to know and the user should hear about it.
    with conn:
        conn.execute("""CREATE TABLE IF NOT EXISTS ref_results (
                            id TEXT PRIMARY KEY,
                            domain_name TEXT,
                            problem_name TEXT,
                            quality INTEGER)""")
    return conn


def _hash_id(domain_text, problem_text):
    # We add the length strings to the hash at the start so that
    # different (domain, problem) pairs that concatenate to the same
    # text can be distinguished. This is a bit paranoid, but better
    # safe than sorry.
    sha1 = hashlib.sha1()
    sha1.update("%d %d " % (len(domain_text), len(problem_text)))
    sha1.update(domain_text)
    sha1.update(problem_text)
    return sha1.hexdigest()


def _lookup_reference_quality(conn, row_id):
    for row in conn.execute(
        "SELECT quality FROM ref_results WHERE id = ?", (row_id,)):
        return row[0]
    else:
        return None


def _update_row(conn, row_id, new_quality):
    conn.execute("UPDATE ref_results SET quality = ? WHERE id = ?",
                 (new_quality, row_id))


def _insert_row(conn, row_id, domain_name, problem_name, quality):
    conn.execute("""INSERT INTO ref_results(
                        id, domain_name, problem_name, quality)
                        VALUES (?, ?, ?, ?)""",
                 (row_id, domain_name, problem_name, quality))


def update_reference_quality(domain_name, domain_text,
                             problem_name, problem_text, quality):
    ## TODO: We should certainly save *the plan*, which right now we
    ##       don't even pass in here.
    ##
    ## TODO: We should keep a permanent record of the various updates.
    ##       One idea would be to use a hg repository for the domains,
    ##       problems and plans, maybe with one directory per hash
    ##       key. This would then obviate the need for a separate log.
    conn = _get_db_connection()
    with conn:
        row_id = _hash_id(domain_text, problem_text)
        previous_best = _lookup_reference_quality(conn, row_id)
        print "previous best quality: %s" % previous_best
        if previous_best is None:
            print "insert new entry"
            _insert_row(conn, row_id, domain_name, problem_name, quality)
        elif quality < previous_best:
            # Lower is better, since our "qualities" are actually costs.
            print "update with improved value"
            _update_row(conn, row_id, quality)
        else:
            print "no improvement"