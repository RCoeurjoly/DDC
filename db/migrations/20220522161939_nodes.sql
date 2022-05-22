-- migrate:up
CREATE TABLE `nodes` (
  `node_id` int unsigned,
  `parent_node_id` int unsigned,
  `birth_order` int unsigned,
  `function_name` blob NOT NULL DEFAULT '',
  `return_value` blob NOT NULL DEFAULT '',
  `object_on_entry` blob NOT NULL DEFAULT '',
  `object_when_returning` blob NOT NULL DEFAULT '',
  `creation_time1` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  `finishing_time` timestamp ON UPDATE CURRENT_TIMESTAMP,
  unique KEY (`node_id`),
  unique KEY (`parent_node_id`, `birth_order`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;

-- migrate:down
DROP TABLE nodes;
