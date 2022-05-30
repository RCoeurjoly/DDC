-- migrate:up

CREATE TABLE `nodes` (
  `id` int unsigned,
  `parent_id` int unsigned,
  `function_name` blob NOT NULL DEFAULT '',
  `return_value` blob DEFAULT NULL,
  `object_on_entry` blob DEFAULT NULL,
  `object_when_returning` blob DEFAULT NULL,
  `creation_time` timestamp(6) DEFAULT NULL,
  `finishing_time` timestamp(6) DEFAULT NULL,
  `finished` boolean NOT NULL DEFAULT false,
  unique KEY (`id`),
  CONSTRAINT `parent_node_exists` FOREIGN KEY (`parent_id`) REFERENCES `nodes` (`id`) ON DELETE CASCADE,
  CONSTRAINT `root_parent_id_zero_otherwise_lower_than_id` CHECK (if(id = 0, parent_id = 0, id > parent_id) = TRUE)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;

-- migrate:down

DROP TABLE nodes;
