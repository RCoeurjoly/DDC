-- migrate:up

CREATE TABLE `nodes` (
  `node_id` int unsigned,
  `parent_node_id` int unsigned,
  `birth_order` int unsigned,
  `function_name` blob NOT NULL DEFAULT '',
  `return_value` blob NOT NULL DEFAULT '',
  `object_on_entry` blob NOT NULL DEFAULT '',
  `object_when_returning` blob NOT NULL DEFAULT '',
  `creation_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  `finishing_time` timestamp ON UPDATE CURRENT_TIMESTAMP,
  `finished` boolean NOT NULL DEFAULT false,
  unique KEY (`node_id`),
  unique KEY (`parent_node_id`, `birth_order`),
  CONSTRAINT `parent_node_exists` FOREIGN KEY (`parent_node_id`) REFERENCES `nodes` (`node_id`),
  CONSTRAINT `parent_node_id_lower_or_equal_node_id` CHECK ((`parent_node_id` <= `node_id`))
) ENGINE=InnoDB DEFAULT CHARSET=latin1;

-- migrate:down

DROP TABLE nodes;
