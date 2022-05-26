-- migrate:up

CREATE TABLE `nodes` (
  `id` int unsigned,
  `parent_id` int unsigned,
  `birth_order` int unsigned,
  `function_name` blob NOT NULL DEFAULT '',
  `return_value` blob NOT NULL DEFAULT '',
  `object_on_entry` blob NOT NULL DEFAULT '',
  `object_when_returning` blob NOT NULL DEFAULT '',
  `creation_time` timestamp(6) NOT NULL DEFAULT CURRENT_TIMESTAMP(6),
  `finishing_time` timestamp(6) ON UPDATE CURRENT_TIMESTAMP(6),
  `finished` boolean NOT NULL DEFAULT false,
  unique KEY (`id`),
  unique KEY (`parent_id`, `birth_order`),
  CONSTRAINT `parent_node_exists` FOREIGN KEY (`parent_id`) REFERENCES `nodes` (`id`) ON DELETE CASCADE,
  CONSTRAINT `root_parent_id_zero_ow_lower_than_id` CHECK (if(id = 0, parent_id = 0, id > parent_id) = TRUE)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;

-- migrate:down

DROP TABLE nodes;
