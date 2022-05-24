-- migrate:up
CREATE TABLE `global_variables_on_entry` (
  `node_id` int unsigned,
  `name` char(255) NOT NULL DEFAULT '',
  `value` blob NOT NULL DEFAULT '',
  unique KEY (`node_id`, `name`),
  CONSTRAINT `global_variables_on_entry_fk_1` FOREIGN KEY (`node_id`) REFERENCES `nodes` (`id`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;

-- migrate:down
DROP TABLE global_variables_on_entry;
